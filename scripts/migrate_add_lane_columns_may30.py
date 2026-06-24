#!/usr/bin/env python3
"""Schema migration: add lane / mathematical_content_score / fusion_json /
informal_mode_used / paired_llm columns to submissions table, and create
a unified `submissions_audit` view.

This is I2 of the May 30 2026 infrastructure series, building on X2's
`closure_axis_json` migration (`scripts/migrate_add_closure_axis.py`).

Columns added:

    lane                        TEXT     -- 'bare' | 'closure' | 'fusion' | 'informal'
    mathematical_content_score  INTEGER  -- 0-10 (F1 "real math vs brute force" axis)
    fusion_json                 TEXT     -- research-fusion dossier metadata
    informal_mode_used          INTEGER  -- 0/1 (Aristotle's informal reasoner invoked?)
    paired_llm                  TEXT     -- strategy LLM ('gpt-5.2-pro', 'codex', 'none', ...)

Backfill rules (prior rows = pre-lane era, all bare-gap mode):

    lane                       <- 'bare'
    informal_mode_used         <- 0
    paired_llm                 <- 'none'
    mathematical_content_score <- NULL  (deferred to I3 audit pass)
    fusion_json                <- NULL  (no fusion before May 30 2026)

Audit backfill (F1 verdicts):

    slot720 -> 5 (structural mild)
    slot722 -> 3 (compute+glue)
    slot736 -> 1 (pure compute, regression)
    slot737 -> 8 (genuine structural)
    slot738 -> 3 (compute+glue)
    slot739 -> 7 (real algebra)

Idempotent: re-running is a no-op. Slot rows that don't yet exist in the DB
are skipped (logged) — they'll be backfilled on first submission/fetch.
"""
import sqlite3
import sys
from pathlib import Path

DB_PATH = Path(__file__).resolve().parent.parent / "submissions" / "tracking.db"


# 5 new columns: (name, sql_type)
NEW_COLUMNS = [
    ("lane",                       "TEXT"),
    ("mathematical_content_score", "INTEGER"),
    ("fusion_json",                "TEXT"),
    ("informal_mode_used",         "INTEGER"),
    ("paired_llm",                 "TEXT"),
]

# F1 verdict backfill keyed by slot prefix (filename LIKE 'slot{N}_%')
F1_VERDICTS = {
    720: 5,  # structural mild
    722: 3,  # compute+glue
    736: 1,  # pure compute, regression
    737: 8,  # genuine structural
    738: 3,  # compute+glue
    739: 7,  # real algebra
}

# SQL view: unified audit join — one row per submission with every audit axis.
# Built as a single SELECT (no joins needed; all audit columns live on
# `submissions` after this migration). Kept as a view so downstream queries
# stay stable even as the underlying table evolves.
AUDIT_VIEW_SQL = """
CREATE VIEW IF NOT EXISTS submissions_audit AS
SELECT
    id,
    uuid,
    filename,
    problem_id,
    status,
    status_legacy,
    submitted_at,
    completed_at,
    lane,
    informal_mode_used,
    paired_llm,
    mathematical_content_score,
    fusion_json,
    closure_axis_json,
    target_resolved,
    axiomatizes_prior_work,
    axiom_count,
    contribution_statement,
    novelty_level,
    experiment_arm,
    sketch_model_primary,
    sketch_model_secondary,
    cost_usd
FROM submissions
"""


def migrate(db_path: Path = DB_PATH) -> dict:
    """Run the migration. Returns a result dict with column add status,
    backfill counts, and F1 backfill detail."""
    conn = sqlite3.connect(str(db_path))
    try:
        # ---- 1. Add columns idempotently ----
        existing = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        added = []
        skipped = []
        for name, sqltype in NEW_COLUMNS:
            if name in existing:
                skipped.append(name)
                continue
            conn.execute(f"ALTER TABLE submissions ADD COLUMN {name} {sqltype}")
            added.append(name)

        # Verify all columns present post-ALTER
        existing = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        for name, _ in NEW_COLUMNS:
            assert name in existing, f"post-migration column missing: {name}"

        # ---- 2. Backfill defaults for pre-lane rows ----
        # 'bare' lane: all submissions before this migration were bare-gap mode.
        bare_backfill = conn.execute(
            "UPDATE submissions SET lane = 'bare' WHERE lane IS NULL"
        ).rowcount
        informal_backfill = conn.execute(
            "UPDATE submissions SET informal_mode_used = 0 WHERE informal_mode_used IS NULL"
        ).rowcount
        paired_backfill = conn.execute(
            "UPDATE submissions SET paired_llm = 'none' WHERE paired_llm IS NULL"
        ).rowcount

        # mathematical_content_score and fusion_json: leave NULL (I3 will backfill).

        # ---- 3. F1 verdict backfill for known advances ----
        f1_results = {}
        for slot, score in F1_VERDICTS.items():
            cur = conn.execute(
                "UPDATE submissions SET mathematical_content_score = ? "
                "WHERE filename LIKE ? AND mathematical_content_score IS NULL",
                (score, f"slot{slot}_%"),
            )
            f1_results[slot] = {"score": score, "rows_updated": cur.rowcount}

        # ---- 4. Create audit view ----
        # Drop and re-create to ensure schema stays in sync if columns ever shift.
        conn.execute("DROP VIEW IF EXISTS submissions_audit")
        conn.execute(AUDIT_VIEW_SQL)

        # ---- 5. Sanity post-migration counts ----
        total = conn.execute("SELECT COUNT(*) FROM submissions").fetchone()[0]
        lane_counts = dict(conn.execute(
            "SELECT lane, COUNT(*) FROM submissions GROUP BY lane"
        ).fetchall())
        score_set = conn.execute(
            "SELECT COUNT(*) FROM submissions WHERE mathematical_content_score IS NOT NULL"
        ).fetchone()[0]

        conn.commit()
    finally:
        conn.close()

    return {
        "columns_added": added,
        "columns_skipped": skipped,
        "bare_backfill_rows": bare_backfill,
        "informal_backfill_rows": informal_backfill,
        "paired_backfill_rows": paired_backfill,
        "f1_backfill": f1_results,
        "total_rows": total,
        "lane_distribution": lane_counts,
        "mcs_set_rows": score_set,
    }


def main() -> int:
    r = migrate()
    if r["columns_added"]:
        print(f"OK  added {len(r['columns_added'])} column(s): {', '.join(r['columns_added'])}")
    if r["columns_skipped"]:
        print(f"OK  already-present (idempotent): {', '.join(r['columns_skipped'])}")
    print(f"    backfill: lane='bare' on {r['bare_backfill_rows']} rows")
    print(f"    backfill: informal_mode_used=0 on {r['informal_backfill_rows']} rows")
    print(f"    backfill: paired_llm='none' on {r['paired_backfill_rows']} rows")
    print(f"    F1 verdict backfill:")
    for slot in sorted(r["f1_backfill"]):
        d = r["f1_backfill"][slot]
        status = "OK" if d["rows_updated"] > 0 else "MISS (slot not in DB)"
        print(f"      slot{slot} score={d['score']}  rows={d['rows_updated']}  [{status}]")
    print(f"    total rows: {r['total_rows']}")
    print(f"    lane distribution: {r['lane_distribution']}")
    print(f"    mathematical_content_score set on: {r['mcs_set_rows']} rows")
    print(f"OK  view submissions_audit (re)created")
    return 0


if __name__ == "__main__":
    sys.exit(main())
