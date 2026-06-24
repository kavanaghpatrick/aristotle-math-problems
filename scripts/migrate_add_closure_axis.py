#!/usr/bin/env python3
"""Schema migration: add closure_axis_json column to submissions table.

Per docs/closure_taxonomy_may30.md (C2's 4-axis taxonomy) and the closure-execution
team contract (Agent #2 of 5, May 30 2026).

Stores per-submission classification as JSON text:

    {
      "CS":  one of {full_closure, direction_closure, disproof_closure,
                     bounded_version_closure, sub_claim_closure, formalization_only},
      "CM":  one of {explicit_witness, bounded_to_infinite_lift,
                     structural_finite_reduction, disproof_construction,
                     witness_table_chunked, density_sieve_closure,
                     induction_template, none_known},
      "CR":  one of {clean_decidable, partial_result_only, iff_rfl_trap,
                     witness_search_explosion, definition_mismatch,
                     em_tautology, infrastructure_overgrowth,
                     recursive_falsification},
      "HM":  one of {journal_clean, journal_partial, journal_subclaim,
                     infrastructure_only},
      "real_closure_candidate": bool,
      "rationale": "<one-sentence justification>"
    }

Idempotent: re-running is a no-op. Prior rows keep closure_axis_json = NULL.
"""
import sqlite3
import sys
from pathlib import Path

DB_PATH = Path(__file__).resolve().parent.parent / "submissions" / "tracking.db"


def migrate(db_path: Path = DB_PATH) -> dict:
    """Add closure_axis_json column. Returns {'added': bool, 'prior_null_count': int}."""
    conn = sqlite3.connect(str(db_path))
    try:
        # Detect existing column
        cols = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        if "closure_axis_json" in cols:
            added = False
        else:
            conn.execute("ALTER TABLE submissions ADD COLUMN closure_axis_json TEXT")
            added = True

        # Verify
        cols = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        assert "closure_axis_json" in cols, "post-migration column missing"

        prior_null_count = conn.execute(
            "SELECT COUNT(*) FROM submissions WHERE closure_axis_json IS NULL"
        ).fetchone()[0]

        conn.commit()
    finally:
        conn.close()

    return {"added": added, "prior_null_count": prior_null_count}


if __name__ == "__main__":
    result = migrate()
    if result["added"]:
        print(f"OK  added closure_axis_json column to submissions")
    else:
        print(f"OK  closure_axis_json already present (idempotent re-run)")
    print(f"    rows with NULL closure_axis_json: {result['prior_null_count']}")
