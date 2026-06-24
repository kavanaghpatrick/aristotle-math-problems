#!/usr/bin/env python3
"""Run a SQLite migration safely.

Usage:
    python3 scripts/migrations/run.py [migration.sql]

If no argument is given, runs the latest 2026_05_28_schema_honesty.sql.

Always:
    1. Backs up tracking.db to tracking.db.bak.<timestamp> before touching anything.
    2. Applies the SQL inside a transaction (the SQL file should manage its own BEGIN/COMMIT).
    3. For the 2026_05_28 migration specifically: after the SQL succeeds, verifies every
       row has status_v2 populated, swaps status_v2 → status (preserving status_legacy),
       and drops the temporary status_v2 column.
    4. Prints before/after row counts grouped by status.
"""

from __future__ import annotations

import shutil
import sqlite3
import sys
from datetime import datetime
from pathlib import Path

DB = Path("submissions/tracking.db")
DEFAULT_SQL = Path("scripts/migrations/2026_05_28_schema_honesty.sql")


def histogram(con: sqlite3.Connection, column: str = "status") -> list[tuple[str, int]]:
    cur = con.execute(f"SELECT {column}, COUNT(*) FROM submissions GROUP BY {column} ORDER BY 2 DESC")
    return list(cur)


def main() -> int:
    sql_path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_SQL
    if not sql_path.exists():
        print(f"FATAL: migration SQL not found: {sql_path}", file=sys.stderr)
        return 2
    if not DB.exists():
        print(f"FATAL: DB not found: {DB}", file=sys.stderr)
        return 2

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup = DB.with_suffix(f".db.bak.{ts}")
    shutil.copy2(DB, backup)
    print(f"backup: {backup} ({backup.stat().st_size:,} bytes)")

    sql = sql_path.read_text()
    con = sqlite3.connect(str(DB))

    print("\nBEFORE migration — status histogram:")
    before = histogram(con, "status")
    for s, n in before:
        print(f"  {s:25} {n:>5}")
    total_before = sum(n for _, n in before)
    print(f"  {'TOTAL':25} {total_before:>5}")

    print(f"\nApplying {sql_path}...")
    con.executescript(sql)
    con.commit()

    # Migration-specific post-step: 2026_05_28 adds status_v2 and we now want
    # to commit to it as the canonical status. status_legacy preserves the original.
    if "status_v2" in sql:
        unmapped = con.execute(
            "SELECT COUNT(*) FROM submissions WHERE status_v2 IS NULL"
        ).fetchone()[0]
        if unmapped:
            print(f"FATAL: {unmapped} rows have NULL status_v2 — refusing to swap.", file=sys.stderr)
            return 3

        con.execute("UPDATE submissions SET status = status_v2")
        con.commit()

        # SQLite supports DROP COLUMN as of 3.35; ours is 3.x. Try it; fall back to noop.
        try:
            con.execute("ALTER TABLE submissions DROP COLUMN status_v2")
            con.commit()
            print("  dropped status_v2 (now redundant with status)")
        except sqlite3.OperationalError as e:
            print(f"  could not DROP COLUMN status_v2: {e} (column harmless, leaving it)")

    print("\nAFTER migration — status histogram:")
    after = histogram(con, "status")
    for s, n in after:
        print(f"  {s:25} {n:>5}")
    total_after = sum(n for _, n in after)
    print(f"  {'TOTAL':25} {total_after:>5}")

    if total_before != total_after:
        print(f"FATAL: row count changed {total_before} → {total_after}", file=sys.stderr)
        return 4

    # Show new column list
    cols = [r[1] for r in con.execute("PRAGMA table_info(submissions)")]
    new_cols = [c for c in cols if c in (
        "axiom_count", "axiomatizes_prior_work", "cost_usd", "status_legacy",
        "sketch_model_primary", "sketch_model_secondary", "sketch_hash",
        "candidate_lemmas_json", "prior_context_used", "experiment_arm",
    )]
    print(f"\nNew/honesty columns now present: {', '.join(new_cols)}")

    print(f"\n✓ migration complete. Backup at {backup}")
    print(f"  Rollback: cp {backup} {DB}")
    con.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
