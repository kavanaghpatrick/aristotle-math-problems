#!/usr/bin/env python3
"""
Generate Aristotle submission files for Erdős problems.
Fetches Lean 4 source, adds informal proof sketch, tracks in database.
"""

import argparse
import json
import sqlite3
import urllib.request
import uuid
from datetime import datetime
from pathlib import Path

DB_PATH = Path(__file__).parent.parent / "submissions" / "tracking.db"
OUTPUT_DIR = Path(__file__).parent.parent / "submissions" / "erdos"

def get_problem_data(conn, problem_number: str):
    """Get problem data from erdos_formal and v_erdos_ready."""
    cursor = conn.cursor()
    cursor.execute("""
        SELECT
            ef.problem_number,
            ef.theorem_name,
            ef.category,
            ef.statement,
            ef.source_url,
            ef.lean_file,
            COALESCE(efu.tractability_score, 50) as tractability,
            COALESCE(efu.status, 'unknown') as problem_status,
            COALESCE(efu.prize, 'no') as prize,
            COALESCE(efu.tags, '[]') as tags
        FROM erdos_formal ef
        LEFT JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.problem_number = ? AND ef.has_sorry = 1
        ORDER BY ef.theorem_name
    """, (problem_number,))
    return cursor.fetchall()

def fetch_lean_source(url: str) -> str:
    """Fetch the original Lean 4 source file."""
    try:
        with urllib.request.urlopen(url) as response:
            return response.read().decode('utf-8')
    except Exception as e:
        print(f"Error fetching {url}: {e}")
        return None

def add_informal_sketch(content: str, theorem_name: str) -> str:
    """Add informal proof sketch placeholder before sorry."""
    # Find the theorem and add a sketch comment
    sketch_template = f"""/-
PROOF SKETCH for {theorem_name}:
1. [TODO: Describe the mathematical approach]
2. [TODO: Key lemmas or techniques needed]
3. [TODO: Why this leads to the result]
-/
"""
    # Insert before the first sorry in the theorem
    if "sorry" in content:
        # Add sketch before the theorem definition
        lines = content.split('\n')
        result = []
        for i, line in enumerate(lines):
            # Insert sketch before theorem/lemma declaration
            if (line.strip().startswith('theorem ' + theorem_name) or
                line.strip().startswith('lemma ' + theorem_name)):
                result.append(sketch_template)
            result.append(line)
        return '\n'.join(result)
    return content

def create_submission_file(problem_number: str, theorem_name: str,
                          lean_content: str, output_dir: Path) -> Path:
    """Create a submission Lean file."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # Clean filename
    safe_name = theorem_name.replace('.', '_').replace(' ', '_')
    filename = f"erdos_{problem_number}_{safe_name}.lean"
    filepath = output_dir / filename

    # Add header comment
    header = f"""/-
Erdős Problem #{problem_number}: {theorem_name}
Source: Google DeepMind Formal Conjectures
Generated: {datetime.now().isoformat()}

Submit via: aristotle --file {filepath}
-/

"""
    with open(filepath, 'w') as f:
        f.write(header + lean_content)

    return filepath

def track_submission(conn, problem_number: str, theorem_name: str,
                    filepath: Path, category: str, prize: str):
    """Track the generated submission in the database."""
    cursor = conn.cursor()
    sub_uuid = str(uuid.uuid4())

    cursor.execute("""
        INSERT INTO submissions
        (uuid, filename, problem_id, pattern, status, sorry_count, notes, created_at, frontier_id)
        VALUES (?, ?, ?, ?, 'draft', 1, ?, datetime('now'), 'erdos')
    """, (
        sub_uuid,
        filepath.name,
        f"erdos_{problem_number}",
        category or 'unknown',
        f"Prize: {prize}. Theorem: {theorem_name}"
    ))

    conn.commit()
    return sub_uuid

def list_top_targets(conn, limit: int = 20):
    """List top submission targets by priority."""
    cursor = conn.cursor()
    cursor.execute("""
        SELECT
            problem_number,
            theorem_name,
            category,
            COALESCE(efu.tractability_score, 50) as tractability,
            COALESCE(efu.status, 'unknown') as status,
            COALESCE(efu.prize, 'no') as prize
        FROM erdos_formal ef
        LEFT JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
        ORDER BY
            CASE WHEN efu.status = 'falsifiable' THEN 0 ELSE 1 END,
            COALESCE(efu.tractability_score, 0) DESC,
            CASE WHEN efu.prize != 'no' THEN 0 ELSE 1 END
        LIMIT ?
    """, (limit,))

    print(f"\n{'#':<6} {'Theorem':<35} {'Status':<12} {'Score':<6} {'Prize':<8}")
    print("-" * 75)
    for row in cursor.fetchall():
        print(f"{row[0]:<6} {row[1][:34]:<35} {row[4]:<12} {row[3]:<6} {row[5]:<8}")

def main():
    parser = argparse.ArgumentParser(description='Generate Erdős problem submissions')
    parser.add_argument('--problem', '-p', help='Problem number to generate')
    parser.add_argument('--list', '-l', action='store_true', help='List top targets')
    parser.add_argument('--limit', type=int, default=20, help='Number of targets to list')
    parser.add_argument('--with-sketch', action='store_true', default=True,
                       help='Add informal proof sketch (recommended)')
    args = parser.parse_args()

    conn = sqlite3.connect(DB_PATH)

    if args.list:
        list_top_targets(conn, args.limit)
        conn.close()
        return

    if not args.problem:
        print("Usage: generate_erdos_submission.py --problem 723")
        print("       generate_erdos_submission.py --list")
        conn.close()
        return

    # Get problem data
    problems = get_problem_data(conn, args.problem)
    if not problems:
        print(f"No theorems found for problem {args.problem}")
        conn.close()
        return

    print(f"\nFound {len(problems)} theorem(s) for Erdős #{args.problem}")

    for prob in problems:
        (problem_number, theorem_name, category, statement,
         source_url, lean_file, tractability, status, prize, tags) = prob

        print(f"\n  Processing: {theorem_name}")
        print(f"  Category: {category}")
        print(f"  Status: {status}, Tractability: {tractability}, Prize: {prize}")

        # Use stored lean_file or fetch fresh
        content = lean_file
        if not content and source_url:
            print(f"  Fetching from {source_url}...")
            content = fetch_lean_source(source_url)

        if not content:
            print(f"  ERROR: No Lean content available")
            continue

        # Add informal sketch
        if args.with_sketch:
            content = add_informal_sketch(content, theorem_name)

        # Create submission file
        filepath = create_submission_file(
            problem_number, theorem_name, content, OUTPUT_DIR
        )
        print(f"  Created: {filepath}")

        # Track in database
        sub_uuid = track_submission(
            conn, problem_number, theorem_name, filepath, category, prize
        )
        print(f"  Tracked: {sub_uuid}")

    conn.close()
    print(f"\nDone! Submit with: aristotle --file <filepath>")

if __name__ == "__main__":
    main()
