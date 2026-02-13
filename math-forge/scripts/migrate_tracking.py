#!/usr/bin/env python3
"""migrate_tracking.py — Bootstrap knowledge.db from tracking.db.

Migrates:
    - proven_theorems -> findings (type: theorem)
    - false_lemmas -> findings (type: false_lemma)
    - failed_approaches -> findings (type: failure)
    - proof_techniques -> used to enrich technique fields
    - candidate_problems -> problems table

Does NOT migrate:
    - Raw .lean result files (too many; extract on-demand via extract_findings.py)
    - Submission metadata (stays in tracking.db as source of truth)
"""

import sqlite3
import sys
import re
import argparse
from pathlib import Path


def migrate(tracking_path: str, knowledge_path: str, schema_path: str):
    # Initialize knowledge.db
    if not Path(knowledge_path).exists():
        import subprocess
        subprocess.run(['sqlite3', knowledge_path], stdin=open(schema_path), check=True)
        print(f"[math-forge] Created knowledge.db")

    t_conn = sqlite3.connect(tracking_path)
    t_conn.row_factory = sqlite3.Row
    k_conn = sqlite3.connect(knowledge_path)

    t = t_conn.cursor()
    k = k_conn.cursor()

    count = 0

    # ---- 1. Migrate proven_theorems ----
    try:
        rows = t.execute("""
            SELECT pt.*, s.filename, s.problem_id, s.uuid
            FROM proven_theorems pt
            LEFT JOIN submissions s ON pt.submission_id = s.id
            WHERE pt.proof_complete = 1
        """).fetchall()

        for row in rows:
            slot = None
            filename = row['filename'] or ''
            slot_match = re.search(r'slot(\d+)', filename)
            if slot_match:
                slot = int(slot_match.group(1))

            try:
                k.execute("""
                    INSERT OR IGNORE INTO findings (
                        finding_type, domain_id, title, description, problem_id,
                        source_slot, source_submission_uuid,
                        theorem_name, theorem_statement,
                        confidence, tags
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    'theorem', 'nt',
                    f"{row['theorem_name']} ({row['theorem_type'] or 'theorem'})",
                    f"Proven {row['theorem_type'] or 'theorem'}: {row['statement'] or row['theorem_name']}",
                    row['problem_id'] or '',
                    slot,
                    row['uuid'],
                    row['theorem_name'],
                    row['statement'],
                    'verified',
                    'migrated',
                ))
                count += 1
            except sqlite3.IntegrityError:
                pass
    except sqlite3.OperationalError as e:
        print(f"[math-forge] WARN: proven_theorems table not found or error: {e}")

    print(f"[math-forge] Migrated {count} proven theorems")

    # ---- 2. Migrate false_lemmas ----
    count2 = 0
    try:
        rows = t.execute("SELECT * FROM false_lemmas").fetchall()

        for row in rows:
            try:
                k.execute("""
                    INSERT OR IGNORE INTO findings (
                        finding_type, domain_id, title, description, problem_id,
                        source_slot,
                        counterexample, why_failed, avoid_pattern,
                        confidence, tags
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    'false_lemma', 'combinatorics',
                    f"FALSE: {row['lemma_name']}",
                    f"Disproven: {row['false_statement_english'] or row['false_statement']}",
                    row['frontier_id'] or '',
                    None,
                    row['counterexample'],
                    row['why_false'],
                    row['avoid_pattern'],
                    'disproven',
                    f"false_lemma,{row['evidence_level']},migrated",
                ))
                count2 += 1
            except sqlite3.IntegrityError:
                pass
    except sqlite3.OperationalError as e:
        print(f"[math-forge] WARN: false_lemmas table not found or error: {e}")

    print(f"[math-forge] Migrated {count2} false lemmas")

    # ---- 3. Migrate failed_approaches ----
    count3 = 0
    try:
        rows = t.execute("SELECT * FROM failed_approaches").fetchall()

        for row in rows:
            slot = None
            if row['submission_uuid']:
                slot_row = t.execute(
                    "SELECT filename FROM submissions WHERE uuid=?",
                    (row['submission_uuid'],)
                ).fetchone()
                if slot_row:
                    slot_match = re.search(r'slot(\d+)', slot_row['filename'] or '')
                    if slot_match:
                        slot = int(slot_match.group(1))

            try:
                k.execute("""
                    INSERT OR IGNORE INTO findings (
                        finding_type, domain_id, title, description, problem_id,
                        source_slot, source_submission_uuid,
                        why_failed, avoid_pattern,
                        confidence, tags, notes
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    'failure', None,
                    f"FAILED: {row['approach_name']}",
                    row['approach_description'],
                    row['problem_id'] or row['frontier_id'] or '',
                    slot,
                    row['submission_uuid'],
                    row['why_failed'],
                    row['avoid_pattern'],
                    'high',
                    f"failure,{row['failure_category'] or 'unknown'},migrated",
                    row['learned_insight'],
                ))
                count3 += 1
            except sqlite3.IntegrityError:
                pass
    except sqlite3.OperationalError as e:
        print(f"[math-forge] WARN: failed_approaches table not found or error: {e}")

    print(f"[math-forge] Migrated {count3} failed approaches")

    # ---- 4. Migrate candidate_problems -> problems ----
    count4 = 0
    try:
        rows = t.execute("SELECT * FROM candidate_problems").fetchall()

        for row in rows:
            domain_map = {
                'number_theory': 'nt', 'nt': 'nt', 'number-theory': 'nt',
                'algebra': 'algebra',
                'combinatorics': 'combinatorics',
                'analysis': 'analysis',
            }
            domain = domain_map.get(row['domain'], 'nt')

            # Map tracking.db statuses to knowledge.db CHECK constraint values
            status_map = {
                'open': 'open', 'candidate': 'open', 'active': 'in_flight',
                'proven': 'proven', 'known_proven': 'proven',
                'known_formalization': 'proven', 'partial': 'partial',
                'rejected': 'open', 'mixed': 'partial', 'false': 'false',
                'disproven': 'false', 'abandoned': 'open', 'in_flight': 'in_flight',
            }
            status = status_map.get(row['status'] or 'open', 'open')

            try:
                k.execute("""
                    INSERT OR IGNORE INTO problems (
                        id, name, domain_id, status,
                        submission_count, proven_count, failed_count,
                        statement
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    row['id'],
                    row['name'],
                    domain,
                    status,
                    row['submissions_count'] or 0,
                    row['proven_count'] or 0,
                    row['false_lemma_count'] or 0,
                    row['statement'],
                ))
                count4 += 1
            except sqlite3.IntegrityError:
                pass
    except sqlite3.OperationalError as e:
        print(f"[math-forge] WARN: candidate_problems table not found or error: {e}")

    print(f"[math-forge] Migrated {count4} candidate problems")

    k_conn.commit()
    k_conn.close()
    t_conn.close()

    total = count + count2 + count3 + count4
    print(f"\n[math-forge] Bootstrap complete: {total} total records migrated to knowledge.db")
    print(f"  Theorems: {count}")
    print(f"  False lemmas: {count2}")
    print(f"  Failed approaches: {count3}")
    print(f"  Problems: {count4}")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Bootstrap knowledge.db from tracking.db')
    parser.add_argument('--tracking-db', default=None, help='Path to tracking.db')
    parser.add_argument('--knowledge-db', default=None, help='Path to knowledge.db')

    args = parser.parse_args()

    plugin_root = Path(__file__).parent.parent
    tracking = args.tracking_db or str(plugin_root.parent / 'submissions' / 'tracking.db')
    knowledge = args.knowledge_db or str(plugin_root / 'data' / 'knowledge.db')
    schema = str(plugin_root / 'data' / 'schema.sql')

    migrate(tracking, knowledge, schema)
