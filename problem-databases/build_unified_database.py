#!/usr/bin/env python3
"""
Build Unified Open Problems Database for Aristotle

Sources:
1. erdosproblems (Terence Tao's repo) - 1111 problems, 640 open
2. formal-conjectures (DeepMind) - 448 pre-formalized Lean 4 files
3. Open Problem Garden (future) - 710+ problems

Output: Consolidated JSON database with tractability scores
"""

import yaml
import json
import os
from pathlib import Path
from collections import defaultdict
from datetime import datetime

BASE_DIR = Path(__file__).parent

def load_erdos_problems():
    """Load and parse Erdős problems from YAML."""
    with open(BASE_DIR / "erdosproblems/data/problems.yaml", 'r') as f:
        raw = yaml.safe_load(f)

    problems = []
    for p in raw:
        problems.append({
            'number': p.get('number', ''),
            'source': 'erdos',
            'status': p.get('status', {}).get('state', 'unknown'),
            'formalized_in_tao_repo': p.get('formalized', {}).get('state', 'no') == 'yes',
            'prize': p.get('prize', 'no'),
            'tags': p.get('tags', []),
            'oeis': p.get('oeis', []),
            'comments': p.get('comments', ''),
            'last_update': p.get('status', {}).get('last_update', ''),
        })

    return problems

def scan_formal_conjectures():
    """Scan DeepMind's formal-conjectures for Lean 4 files."""
    base = BASE_DIR / "formal-conjectures/FormalConjectures"

    problems = []
    erdos_lean_files = {}  # Map Erdős number to lean file

    for lean_file in base.rglob("*.lean"):
        if lean_file.name == "All.lean" or "Util" in str(lean_file):
            continue

        rel_path = lean_file.relative_to(base)
        category = rel_path.parts[0] if len(rel_path.parts) > 1 else "Root"

        # Read first 50 lines for metadata
        try:
            with open(lean_file, 'r') as f:
                content = f.read(2000)  # First 2KB
        except:
            content = ""

        # Extract problem name
        name = lean_file.stem

        # Check if it's an Erdős problem
        is_erdos = category == "ErdosProblems"
        erdos_num = name if is_erdos and name.isdigit() else None

        if erdos_num:
            erdos_lean_files[erdos_num] = str(lean_file)

        problems.append({
            'name': name,
            'source': 'formal-conjectures',
            'category': category,
            'lean_file': str(lean_file),
            'has_lean4': True,
            'erdos_number': erdos_num,
            'content_preview': content[:500] if content else '',
        })

    return problems, erdos_lean_files

def estimate_tractability(problem):
    """
    Estimate tractability score (0-100) based on heuristics.

    Factors:
    - Formalized in Lean 4 (+30)
    - Has OEIS sequence (+10) - bounded/computational
    - Tags suggest combinatorics/graph theory (+10)
    - Prize amount (inverse correlation with difficulty)
    - Recent progress
    """
    score = 50  # Base score

    # Has Lean 4 file
    if problem.get('has_lean4') or problem.get('lean_file'):
        score += 30

    # Formalized in Tao's repo
    if problem.get('formalized_in_tao_repo'):
        score += 10

    # Has OEIS sequence (suggests bounded/computational)
    oeis = problem.get('oeis', [])
    if oeis and oeis != ['N/A']:
        score += 10

    # Tags analysis
    tags = problem.get('tags', [])
    tractable_tags = ['combinatorics', 'graph theory', 'sidon sets', 'additive basis']
    hard_tags = ['number theory', 'primes']  # Often intractable

    for tag in tags:
        tag_lower = tag.lower()
        if any(t in tag_lower for t in tractable_tags):
            score += 5
        if 'primes' in tag_lower or 'twin prime' in tag_lower:
            score -= 10  # Prime problems are notoriously hard

    # Prize analysis (high prizes often mean hard problems)
    prize = problem.get('prize', 'no')
    if prize == 'no' or prize == '':
        score += 5  # No prize might mean more tractable
    elif prize and '$' in str(prize):
        try:
            amount = int(prize.replace('$', '').replace(',', ''))
            if amount >= 5000:
                score -= 15  # Very hard
            elif amount >= 1000:
                score -= 5  # Hard
        except:
            pass

    # Clamp to 0-100
    return max(0, min(100, score))

def build_unified_database():
    """Build the unified database."""
    print("=" * 70)
    print("BUILDING UNIFIED OPEN PROBLEMS DATABASE")
    print("=" * 70)
    print()

    # Load sources
    print("Loading Erdős problems...")
    erdos_problems = load_erdos_problems()
    print(f"  Loaded {len(erdos_problems)} problems")

    print("Scanning formal-conjectures...")
    formal_problems, erdos_lean_files = scan_formal_conjectures()
    print(f"  Found {len(formal_problems)} Lean 4 files")
    print(f"  Mapped {len(erdos_lean_files)} Erdős numbers to Lean files")

    # Cross-reference Erdős problems with Lean files
    print("\nCross-referencing...")
    for p in erdos_problems:
        num = p['number']
        if num in erdos_lean_files:
            p['lean_file'] = erdos_lean_files[num]
            p['has_lean4'] = True
        else:
            p['has_lean4'] = False

    # Calculate tractability scores
    print("Calculating tractability scores...")
    for p in erdos_problems:
        p['tractability_score'] = estimate_tractability(p)

    for p in formal_problems:
        p['tractability_score'] = estimate_tractability(p)

    # Build unified database
    database = {
        'metadata': {
            'created': datetime.now().isoformat(),
            'sources': ['erdosproblems', 'formal-conjectures'],
            'total_erdos': len(erdos_problems),
            'total_formal': len(formal_problems),
        },
        'erdos_problems': erdos_problems,
        'formal_conjectures': formal_problems,
    }

    # Statistics
    open_erdos = [p for p in erdos_problems if p['status'] == 'open']
    open_with_lean = [p for p in open_erdos if p['has_lean4']]
    high_tractability = [p for p in open_with_lean if p['tractability_score'] >= 70]

    print()
    print("=" * 70)
    print("DATABASE STATISTICS")
    print("=" * 70)
    print(f"Erdős Problems: {len(erdos_problems)}")
    print(f"  Open: {len(open_erdos)}")
    print(f"  Open + Has Lean 4: {len(open_with_lean)} ⭐")
    print(f"  Open + Lean 4 + High Tractability (≥70): {len(high_tractability)} ⭐⭐")
    print()
    print(f"Formal Conjectures: {len(formal_problems)}")
    print(f"  From ErdosProblems: {len(erdos_lean_files)}")
    print(f"  From Wikipedia: {len([p for p in formal_problems if p['category'] == 'Wikipedia'])}")
    print(f"  From arXiv: {len([p for p in formal_problems if p['category'] == 'Arxiv'])}")
    print()

    # Save database
    output_path = BASE_DIR / "unified_problems_database.json"
    with open(output_path, 'w') as f:
        json.dump(database, f, indent=2, default=str)
    print(f"Database saved to: {output_path}")

    # Create top candidates CSV for easy viewing
    print("\n" + "=" * 70)
    print("TOP 50 CANDIDATES (Open + Lean 4, sorted by tractability)")
    print("=" * 70)

    top_candidates = sorted(open_with_lean, key=lambda x: -x['tractability_score'])[:50]

    csv_path = BASE_DIR / "top_candidates.csv"
    with open(csv_path, 'w') as f:
        f.write("rank,erdos_number,tractability,prize,tags,has_lean4,oeis\n")
        for i, p in enumerate(top_candidates, 1):
            tags = ';'.join(p.get('tags', []))[:50]
            oeis = ';'.join(p.get('oeis', []) if isinstance(p.get('oeis'), list) else [])
            f.write(f"{i},{p['number']},{p['tractability_score']},{p['prize']},\"{tags}\",{p['has_lean4']},{oeis}\n")

            if i <= 20:
                print(f"  {i:2}. Erdős #{p['number']:4} | Score: {p['tractability_score']} | Prize: {p['prize']:6} | Tags: {tags[:40]}")

    print(f"\nFull list saved to: {csv_path}")

    # Save top candidates as JSON too
    top_json_path = BASE_DIR / "top_50_candidates.json"
    with open(top_json_path, 'w') as f:
        json.dump(top_candidates, f, indent=2, default=str)
    print(f"Top 50 JSON saved to: {top_json_path}")

    return database

if __name__ == "__main__":
    db = build_unified_database()
