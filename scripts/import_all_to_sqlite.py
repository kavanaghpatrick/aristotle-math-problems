#!/usr/bin/env python3
"""
Import all JSON data into SQLite database.
Creates proper tables and archives source files.
"""

import sqlite3
import json
import os
import shutil
from pathlib import Path
from datetime import datetime

DB_PATH = "/Users/patrickkavanagh/math/submissions/tracking.db"
ARCHIVE_PATH = "/Users/patrickkavanagh/math/archive/json_import_" + datetime.now().strftime("%Y%m%d_%H%M%S")

def connect_db():
    return sqlite3.connect(DB_PATH)

def create_tables(conn):
    """Create new tables for all data types."""
    cursor = conn.cursor()

    # Erdős problems table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS erdos_problems (
        num INTEGER PRIMARY KEY,
        score INTEGER,
        open INTEGER,
        answer_sorry INTEGER,
        decide INTEGER,
        finite INTEGER,
        asymptotics INTEGER,
        prize INTEGER,
        theorems TEXT,  -- JSON array
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    # Erdős attempts tracking
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS erdos_attempts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        problem_num INTEGER NOT NULL,
        prize TEXT,
        topic TEXT,
        status TEXT,
        attempts INTEGER DEFAULT 0,
        result TEXT,
        uuid TEXT,
        notes TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (problem_num) REFERENCES erdos_problems(num)
    )
    """)

    # Full Erdős+Formal Conjectures unified database
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS erdos_full (
        number TEXT PRIMARY KEY,
        source TEXT,
        status TEXT,
        formalized_in_tao_repo INTEGER,
        prize TEXT,
        tags TEXT,  -- JSON array
        oeis TEXT,  -- JSON array
        comments TEXT,
        last_update TEXT,
        lean_file TEXT,
        has_lean4 INTEGER,
        tractability_score INTEGER,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    # Algorithm discovery candidates
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS algorithm_candidates (
        id TEXT PRIMARY KEY,
        name TEXT NOT NULL,
        category TEXT,
        upper_bound TEXT,
        upper_source TEXT,
        lower_bound TEXT,
        lower_source TEXT,
        gap TEXT,
        tractability_score INTEGER,
        search_space TEXT,
        why_hard TEXT,
        prior_ai_success TEXT,
        practical_impact TEXT,
        problem_type TEXT,  -- asymptotic or finite_instance
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    # Papers table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS papers (
        id TEXT PRIMARY KEY,
        title TEXT NOT NULL,
        authors TEXT,  -- JSON array
        year INTEGER,
        arxiv TEXT,
        doi TEXT,
        publication TEXT,
        status TEXT DEFAULT 'extracted',
        relevance_to_nu4 TEXT,
        main_result TEXT,
        key_insight TEXT,
        why_it_fails_nu4 TEXT,
        formalization_status TEXT,
        notes TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    # Literature lemmas table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS literature_lemmas (
        id TEXT PRIMARY KEY,
        paper_id TEXT NOT NULL,
        name TEXT NOT NULL,
        source_ref TEXT,
        type TEXT,  -- definition, lemma, theorem
        statement TEXT,
        english TEXT,
        proof_status TEXT,  -- proven, axiom, pending
        proof_uuid TEXT,
        proof_file TEXT,
        proof_technique TEXT,
        validated INTEGER DEFAULT 0,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (paper_id) REFERENCES papers(id)
    )
    """)

    # Frontiers table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS frontiers (
        id TEXT PRIMARY KEY,
        name TEXT NOT NULL,
        status TEXT DEFAULT 'open',
        priority INTEGER,
        summary TEXT,
        key_question TEXT,
        our_advantages TEXT,  -- JSON array
        risk_assessment TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    # Frontier submissions junction table
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS frontier_submissions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        frontier_id TEXT NOT NULL,
        submission_uuid TEXT NOT NULL,
        submission_type TEXT,  -- formal, informal
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (frontier_id) REFERENCES frontiers(id),
        FOREIGN KEY (submission_uuid) REFERENCES submissions(uuid)
    )
    """)

    # Frontier applicable lemmas
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS frontier_lemmas (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        frontier_id TEXT NOT NULL,
        lemma_name TEXT NOT NULL,
        lemma_status TEXT,
        lemma_uuid TEXT,
        applicability TEXT,
        how_to_use TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (frontier_id) REFERENCES frontiers(id)
    )
    """)

    # New lemmas needed for frontiers
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS frontier_needed_lemmas (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        frontier_id TEXT NOT NULL,
        name TEXT NOT NULL,
        statement TEXT,
        target_statement TEXT,
        why_needed TEXT,
        proof_approach TEXT,
        status TEXT DEFAULT 'needed',
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (frontier_id) REFERENCES frontiers(id)
    )
    """)

    # Counterexample constraints
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS counterexample_constraints (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        source TEXT,
        constraint_text TEXT NOT NULL,
        lean_formalization TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """)

    conn.commit()
    print("✓ Tables created")

def import_papers(conn, papers_dir):
    """Import all paper JSON files."""
    cursor = conn.cursor()
    imported = 0

    for json_file in Path(papers_dir).glob("*.json"):
        with open(json_file) as f:
            data = json.load(f)

        # Insert paper
        cursor.execute("""
        INSERT OR REPLACE INTO papers (
            id, title, authors, year, arxiv, doi, publication,
            status, relevance_to_nu4, main_result, key_insight,
            why_it_fails_nu4, formalization_status, notes
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            data.get('id'),
            data.get('title', json_file.stem),
            json.dumps(data.get('authors', [])),
            data.get('year'),
            data.get('arxiv'),
            data.get('doi'),
            data.get('publication'),
            data.get('status', 'extracted'),
            data.get('relevance_to_nu4'),
            data.get('main_result'),
            data.get('key_insight'),
            data.get('why_it_fails_nu4'),
            data.get('formalization_status'),
            data.get('notes')
        ))

        # Insert lemmas if present
        for lemma in data.get('lemmas', []):
            cursor.execute("""
            INSERT OR REPLACE INTO literature_lemmas (
                id, paper_id, name, source_ref, type, statement,
                english, proof_status, proof_uuid, proof_file,
                proof_technique, validated
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                lemma.get('id'),
                data.get('id'),
                lemma.get('name'),
                lemma.get('source_ref'),
                lemma.get('type'),
                lemma.get('statement'),
                lemma.get('english'),
                lemma.get('proof_status'),
                json.dumps(lemma.get('proof_uuid')) if isinstance(lemma.get('proof_uuid'), list) else lemma.get('proof_uuid'),
                lemma.get('proof_file'),
                lemma.get('proof_technique'),
                1 if lemma.get('validated') else 0
            ))

        imported += 1

    conn.commit()
    print(f"✓ Imported {imported} papers with lemmas")

def import_frontiers(conn, frontiers_dir):
    """Import frontier research data."""
    cursor = conn.cursor()

    # Load main index
    index_file = Path(frontiers_dir) / "index.json"
    if not index_file.exists():
        print("✗ No frontiers index.json found")
        return

    with open(index_file) as f:
        index_data = json.load(f)

    for frontier in index_data.get('frontiers', []):
        # Insert frontier
        cursor.execute("""
        INSERT OR REPLACE INTO frontiers (
            id, name, status, priority, summary, key_question,
            our_advantages, risk_assessment
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            frontier.get('id'),
            frontier.get('name'),
            frontier.get('status'),
            frontier.get('priority'),
            frontier.get('summary'),
            frontier.get('key_question'),
            json.dumps(frontier.get('our_advantages', [])),
            frontier.get('risk_assessment')
        ))

        # Link submissions
        submissions = frontier.get('submissions', {})
        if submissions:
            for sub_type, sub_data in submissions.items():
                if sub_data and sub_data.get('uuid'):
                    cursor.execute("""
                    INSERT OR IGNORE INTO frontier_submissions (
                        frontier_id, submission_uuid, submission_type
                    ) VALUES (?, ?, ?)
                    """, (frontier.get('id'), sub_data.get('uuid'), sub_type))

        # Import lemmas from subdirectory
        lemmas_file = Path(frontiers_dir) / frontier.get('id') / "lemmas.json"
        if lemmas_file.exists():
            with open(lemmas_file) as f:
                lemmas_data = json.load(f)

            for lemma in lemmas_data.get('our_applicable_lemmas', []):
                cursor.execute("""
                INSERT OR IGNORE INTO frontier_lemmas (
                    frontier_id, lemma_name, lemma_status, lemma_uuid,
                    applicability, how_to_use
                ) VALUES (?, ?, ?, ?, ?, ?)
                """, (
                    frontier.get('id'),
                    lemma.get('name'),
                    lemma.get('status'),
                    lemma.get('uuid'),
                    lemma.get('applicability'),
                    lemma.get('how_to_use')
                ))

            for needed in lemmas_data.get('new_lemmas_needed', []):
                cursor.execute("""
                INSERT OR IGNORE INTO frontier_needed_lemmas (
                    frontier_id, name, statement, target_statement,
                    why_needed, proof_approach
                ) VALUES (?, ?, ?, ?, ?, ?)
                """, (
                    frontier.get('id'),
                    needed.get('name'),
                    needed.get('statement'),
                    needed.get('target_statement'),
                    needed.get('why_needed'),
                    needed.get('proof_approach')
                ))

    conn.commit()
    print(f"✓ Imported {len(index_data.get('frontiers', []))} frontiers with lemmas")

def import_counterexample_constraints(conn, db_dir):
    """Import counterexample constraints from index.json."""
    cursor = conn.cursor()

    index_file = Path(db_dir) / "index.json"
    if not index_file.exists():
        return

    with open(index_file) as f:
        data = json.load(f)

    constraints = data.get('counterexample_constraints', {}).get('from_literature', [])
    for constraint in constraints:
        cursor.execute("""
        INSERT OR IGNORE INTO counterexample_constraints (source, constraint_text)
        VALUES ('literature', ?)
        """, (constraint,))

    conn.commit()
    print(f"✓ Imported {len(constraints)} counterexample constraints")

def import_erdos_problems(conn, problems_dir):
    """Import Erdős problem scoring data."""
    cursor = conn.cursor()

    # Import solvable_open.json
    solvable_file = Path(problems_dir) / "solvable_open.json"
    if solvable_file.exists():
        with open(solvable_file) as f:
            problems = json.load(f)

        for p in problems:
            cursor.execute("""
            INSERT OR REPLACE INTO erdos_problems (
                num, score, open, answer_sorry, decide, finite,
                asymptotics, prize, theorems
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                p.get('num'),
                p.get('score'),
                p.get('open'),
                1 if p.get('answer_sorry') else 0,
                1 if p.get('decide') else 0,
                1 if p.get('finite') else 0,
                1 if p.get('asymptotics') else 0,
                p.get('prize'),
                json.dumps(p.get('theorems', []))
            ))

        print(f"✓ Imported {len(problems)} Erdős problems from solvable_open.json")

    # Import unified_problems_database.json
    unified_file = Path(problems_dir) / "unified_problems_database.json"
    if unified_file.exists():
        with open(unified_file) as f:
            data = json.load(f)

        for p in data.get('erdos_problems', []):
            # Handle fields that might be lists
            def to_str(val):
                if val is None:
                    return None
                if isinstance(val, (list, dict)):
                    return json.dumps(val)
                return str(val)

            cursor.execute("""
            INSERT OR REPLACE INTO erdos_full (
                number, source, status, formalized_in_tao_repo, prize,
                tags, oeis, comments, last_update, lean_file, has_lean4,
                tractability_score
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                str(p.get('number')),
                p.get('source'),
                p.get('status'),
                1 if p.get('formalized_in_tao_repo') else 0,
                to_str(p.get('prize')),
                to_str(p.get('tags', [])),
                to_str(p.get('oeis', [])),
                to_str(p.get('comments')),
                p.get('last_update'),
                p.get('lean_file'),
                1 if p.get('has_lean4') else 0,
                p.get('tractability_score')
            ))

        print(f"✓ Imported {len(data.get('erdos_problems', []))} problems from unified_problems_database.json")

    # Import algorithms.json
    algo_file = Path(problems_dir) / "algorithms.json"
    if algo_file.exists():
        with open(algo_file) as f:
            data = json.load(f)

        count = 0
        for prob_type in ['asymptotic_problems', 'finite_instances']:
            problems = data.get(prob_type, {}).get('problems', [])
            for p in problems:
                cursor.execute("""
                INSERT OR REPLACE INTO algorithm_candidates (
                    id, name, category, upper_bound, upper_source,
                    lower_bound, lower_source, gap, tractability_score,
                    search_space, why_hard, prior_ai_success, practical_impact,
                    problem_type
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    p.get('id'),
                    p.get('name'),
                    p.get('category'),
                    p.get('upper_bound'),
                    p.get('upper_source'),
                    p.get('lower_bound'),
                    p.get('lower_source'),
                    p.get('gap'),
                    p.get('tractability_score'),
                    p.get('search_space'),
                    p.get('why_hard'),
                    p.get('prior_ai_success'),
                    p.get('practical_impact'),
                    prob_type.replace('_problems', '').replace('_instances', '')
                ))
                count += 1

        print(f"✓ Imported {count} algorithm candidates from algorithms.json")

    conn.commit()

def import_erdos_attempts(conn, submissions_dir):
    """Import Erdős attempt tracking data."""
    cursor = conn.cursor()

    attempts_file = Path(submissions_dir) / "erdos_attempts.json"
    if not attempts_file.exists():
        return

    with open(attempts_file) as f:
        data = json.load(f)

    problems = data.get('problems', {})
    imported = 0

    for num, p in problems.items():
        cursor.execute("""
        INSERT OR REPLACE INTO erdos_attempts (
            problem_num, prize, topic, status, attempts, result, uuid, notes
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            int(num),
            p.get('prize'),
            p.get('topic'),
            p.get('status'),
            p.get('attempts', 0),
            p.get('result'),
            p.get('uuid'),
            p.get('notes')
        ))
        imported += 1

    conn.commit()
    print(f"✓ Imported {imported} Erdős attempt records")

def archive_json_files(sources):
    """Move imported JSON directories to archive."""
    os.makedirs(ARCHIVE_PATH, exist_ok=True)

    for source in sources:
        if os.path.exists(source):
            dest = os.path.join(ARCHIVE_PATH, os.path.basename(source))
            shutil.move(source, dest)
            print(f"✓ Archived {source} → {dest}")

def main():
    print("=" * 60)
    print("IMPORTING ALL JSON DATA TO SQLITE")
    print("=" * 60)

    conn = connect_db()

    # Create tables
    create_tables(conn)

    # Import papers
    papers_dir = "/Users/patrickkavanagh/math/db/papers"
    if os.path.exists(papers_dir):
        import_papers(conn, papers_dir)

    # Import frontiers
    frontiers_dir = "/Users/patrickkavanagh/math/docs/research/frontiers"
    if os.path.exists(frontiers_dir):
        import_frontiers(conn, frontiers_dir)

    # Import counterexample constraints
    db_dir = "/Users/patrickkavanagh/math/db"
    import_counterexample_constraints(conn, db_dir)

    # Import Erdős problems
    problems_dir = "/Users/patrickkavanagh/math/problem-databases"
    if os.path.exists(problems_dir):
        import_erdos_problems(conn, problems_dir)

    # Import Erdős attempts
    submissions_dir = "/Users/patrickkavanagh/math/submissions"
    import_erdos_attempts(conn, submissions_dir)

    conn.close()

    # Show summary
    print("\n" + "=" * 60)
    print("IMPORT COMPLETE - Database summary:")
    print("=" * 60)

    conn = connect_db()
    cursor = conn.cursor()

    tables = ['papers', 'literature_lemmas', 'frontiers', 'frontier_submissions',
              'frontier_lemmas', 'frontier_needed_lemmas', 'counterexample_constraints',
              'erdos_problems', 'erdos_attempts', 'erdos_full', 'algorithm_candidates',
              'submissions', 'proven_theorems']

    for table in tables:
        try:
            cursor.execute(f"SELECT COUNT(*) FROM {table}")
            count = cursor.fetchone()[0]
            print(f"  {table}: {count} rows")
        except:
            pass

    conn.close()

    print("\n" + "=" * 60)
    print("READY TO ARCHIVE SOURCE FILES")
    print("Run with --archive flag to move JSON files to archive")
    print("=" * 60)

if __name__ == "__main__":
    import sys
    main()

    if "--archive" in sys.argv:
        archive_sources = [
            "/Users/patrickkavanagh/math/db/papers",
            "/Users/patrickkavanagh/math/docs/research/frontiers",
            "/Users/patrickkavanagh/math/db/index.json",
            "/Users/patrickkavanagh/math/db/prioritization_nu4.json",
            "/Users/patrickkavanagh/math/db/schema.json",
            "/Users/patrickkavanagh/math/problem-databases/solvable_open.json",
            "/Users/patrickkavanagh/math/problem-databases/boris_scores.json",
            "/Users/patrickkavanagh/math/problem-databases/enriched_problems.json",
            "/Users/patrickkavanagh/math/problem-databases/intelligent_scoring_results.json",
            "/Users/patrickkavanagh/math/problem-databases/top_50_candidates.json",
            "/Users/patrickkavanagh/math/problem-databases/unified_problems_database.json",
            "/Users/patrickkavanagh/math/problem-databases/algorithms.json",
            "/Users/patrickkavanagh/math/submissions/erdos_attempts.json",
        ]
        archive_json_files(archive_sources)
