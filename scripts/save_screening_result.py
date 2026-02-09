#!/usr/bin/env python3
"""Save a screening result to the candidate_problems DB table."""
import sqlite3
import sys
import json
from pathlib import Path

DB_PATH = Path(__file__).parent.parent / "submissions" / "tracking.db"

def save_result(data: dict):
    """Insert or update a candidate_problems row from screening data."""
    required = ['id', 'name', 'domain', 'statement']
    for k in required:
        if k not in data:
            print(f"ERROR: Missing required field '{k}'")
            return False

    conn = sqlite3.connect(str(DB_PATH))
    cur = conn.cursor()

    cur.execute("""
        INSERT INTO candidate_problems (
            id, name, domain, statement, lean_statement, source, source_url,
            score_domain, score_proof_structure, score_mathlib, score_finite,
            score_length, score_precedent, score_interest,
            status, approach, blockers, notes
        ) VALUES (
            :id, :name, :domain, :statement, :lean_statement, :source, :source_url,
            :score_domain, :score_proof_structure, :score_mathlib, :score_finite,
            :score_length, :score_precedent, :score_interest,
            :status, :approach, :blockers, :notes
        )
        ON CONFLICT(id) DO UPDATE SET
            name=excluded.name, domain=excluded.domain,
            statement=excluded.statement, lean_statement=excluded.lean_statement,
            source=excluded.source, source_url=excluded.source_url,
            score_domain=excluded.score_domain,
            score_proof_structure=excluded.score_proof_structure,
            score_mathlib=excluded.score_mathlib,
            score_finite=excluded.score_finite,
            score_length=excluded.score_length,
            score_precedent=excluded.score_precedent,
            score_interest=excluded.score_interest,
            status=excluded.status, approach=excluded.approach,
            blockers=excluded.blockers, notes=excluded.notes,
            updated_at=CURRENT_TIMESTAMP
    """, {
        'id': data['id'],
        'name': data['name'],
        'domain': data['domain'],
        'statement': data['statement'],
        'lean_statement': data.get('lean_statement', ''),
        'source': data.get('source', ''),
        'source_url': data.get('source_url', ''),
        'score_domain': data.get('score_domain', 0),
        'score_proof_structure': data.get('score_proof_structure', 0),
        'score_mathlib': data.get('score_mathlib', 0),
        'score_finite': data.get('score_finite', 0),
        'score_length': data.get('score_length', 0),
        'score_precedent': data.get('score_precedent', 0),
        'score_interest': data.get('score_interest', 0),
        'status': data.get('status', 'candidate'),
        'approach': data.get('approach', ''),
        'blockers': data.get('blockers', ''),
        'notes': data.get('notes', ''),
    })

    conn.commit()
    conn.close()
    composite = (
        0.20 * data.get('score_domain', 0) +
        0.20 * data.get('score_proof_structure', 0) +
        0.15 * data.get('score_mathlib', 0) +
        0.15 * data.get('score_finite', 0) +
        0.10 * data.get('score_length', 0) +
        0.10 * data.get('score_precedent', 0) +
        0.10 * data.get('score_interest', 0)
    )
    print(f"OK: Saved '{data['name']}' → composite={composite:.2f}")
    return True


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python3 save_screening_result.py '<json>'")
        print("  or pipe JSON: echo '{...}' | python3 save_screening_result.py -")
        sys.exit(1)

    if sys.argv[1] == '-':
        data = json.load(sys.stdin)
    else:
        data = json.loads(sys.argv[1])

    if isinstance(data, list):
        for d in data:
            save_result(d)
    else:
        save_result(data)
