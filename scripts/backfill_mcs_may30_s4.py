#!/usr/bin/env python3
"""Backfill mathematical_content_score for slot 736-740 and 741-746 (S4 audit).

The original I2 migration backfilled mcs for filenames matching `slot{N}_%`,
but slots 736-739 did not have DB rows at that time and slot 740 was missing
from F1's verdict map. S4's audit (May 30) reconciles:

  slot736 = 1  PURE COMPUTE
  slot737 = 8  STRUCTURAL (real σ₀ multiplicativity)
  slot738 = 3  COMPUTE + GLUE
  slot739 = 7  real algebra
  slot740 = 2  Python external + native_decide (structural plan, compute proof)

For slots 736-740: rows are still not present in DB (these were direct CLI
submissions not yet tracked).  We DO NOT fabricate DB rows.  Instead we
record the intended verdict in a sidecar table (`mcs_pending_backfill`) so
that when the rows eventually land (next /track or /fetch), the value is
applied automatically.

For slots 741-746: these are the new closure-axis-aware May 30 batch.  The
multiperfect submission (slot 746) is already in DB as row 1258. Slots
741-745 were submitted via direct project IDs without DB tracking and
their rows do not yet exist.  Same treatment: queue the score.

This script is idempotent.  Re-running performs no UPDATE if the score is
already set (or already queued).
"""
import json
import sqlite3
import sys
from pathlib import Path

DB_PATH = Path(__file__).resolve().parent.parent / "submissions" / "tracking.db"

# Final S4 verdicts (May 30 2026).  Numeric on 0-10 (F1 axis):
#   0 = pure brute force
#   3 = compute + structural glue
#   5 = structural mild
#   7 = real algebra
#  10 = deep structural insight
S4_VERDICTS = {
    "slot736": (1, "PURE COMPUTE (F1 verdict)"),
    "slot737": (8, "STRUCTURAL — real σ₀ multiplicativity"),
    "slot738": (3, "COMPUTE + GLUE"),
    "slot739": (7, "real algebra"),
    "slot740": (2, "Python external + native_decide; structural plan but compute proof"),
}

# Slot 741-746 (May 30 closure-axis batch).
# UUIDs from aristotle_submission_log.jsonl.
NEW_BATCH = {
    "slot741": {
        "uuid": "7031f637-54ed-4362-9456-5b4e27e038e0",
        "filename": "erdos647_cunningham_residual_35",
        "problem_id": "erdos_647",
        "lane": "closure",
        "mcs": 6,
        "mcs_note": "Sub-claim closure — finite witness cascade over 35 verified n; structural reduction inherited from slot737, witness table is compute. Sub-claim is real and publishable.",
    },
    "slot742": {
        "uuid": "bdc60eff-04a7-4c15-b469-bcd118b443c6",
        "filename": "erdos203_sierpinski_1d_benchmark",
        "problem_id": "erdos_203",
        "lane": "bare",
        "mcs": 1,
        "mcs_note": "Calibration / formalization-only benchmark; 1-D Sierpinski coverings are classical.",
    },
    "slot743": {
        "uuid": "8d9e29b3-c099-4fea-beb2-aab7ed76fb99",
        "filename": "erdos203_grid_12x12_B1000",
        "problem_id": "erdos_203",
        "lane": "bare",
        "mcs": 2,
        "mcs_note": "Bounded extension of slot740; honest hedge — likely unsatisfiable (MC coverage 0.751). Pure compute.",
    },
    "slot744": {
        "uuid": "22dafcc6-0afa-4769-b293-c368b97ade0b",
        "filename": "FT_p3_q1583_alternate",
        "problem_id": "feit_thompson",
        "lane": "closure",
        "mcs": 5,
        "mcs_note": "Single-q sub-claim closure for FT p=3 q=1583; structurally meaningful (family-boundary prime).",
    },
    "slot745": {
        "uuid": "8e353fc6-c165-4df2-9577-088dea34eb52",
        "filename": "brocard_nrange_1001_2000",
        "problem_id": "brocard",
        "lane": "bare",
        "mcs": 2,
        "mcs_note": "Range-bump bounded version of slot722; chunked native_decide.",
    },
    "slot746": {
        "uuid": "65da8d8c-4059-4454-b3b4-ea2e3b87ede7",
        "filename": "odd_multiperfect_sigma0_11",
        "problem_id": "odd_multiperfect",
        "lane": "closure",
        "mcs": 4,
        "mcs_note": "Sub-claim closure via 1-line p-adic from slot737 multiplicativity DNA; structurally clean, application is light.",
    },
}


def ensure_pending_table(conn):
    """Create the sidecar pending-backfill table if missing."""
    conn.execute("""
        CREATE TABLE IF NOT EXISTS mcs_pending_backfill (
            slot TEXT PRIMARY KEY,
            uuid TEXT,
            filename TEXT,
            problem_id TEXT,
            lane TEXT,
            mathematical_content_score INTEGER,
            note TEXT,
            queued_at TEXT DEFAULT CURRENT_TIMESTAMP,
            applied_at TEXT
        )
    """)


def apply_pending(conn):
    """For every queued row in mcs_pending_backfill, try to find the matching
    submissions row and update it; mark applied_at when done.

    Match priority:
      1. uuid match (most reliable)
      2. filename LIKE '%slot{N}%' or filename LIKE '%{filename_stem}%'
    """
    cur = conn.execute("""
        SELECT slot, uuid, filename, problem_id, lane,
               mathematical_content_score, note
          FROM mcs_pending_backfill
         WHERE applied_at IS NULL
    """)
    pending = cur.fetchall()
    applied_count = 0

    for (slot, uuid, filename, problem_id, lane, mcs, note) in pending:
        # Try uuid match first
        target_id = None
        if uuid:
            r = conn.execute(
                "SELECT id FROM submissions WHERE uuid = ?",
                (uuid,),
            ).fetchone()
            if r:
                target_id = r[0]
        # Fallback: filename match
        if target_id is None and filename:
            r = conn.execute(
                "SELECT id FROM submissions WHERE filename = ? "
                "OR filename LIKE ? ORDER BY submitted_at DESC LIMIT 1",
                (filename, f"%{filename}%"),
            ).fetchone()
            if r:
                target_id = r[0]
        # Fallback: slot-prefix match (filename starts with slot{N}_)
        if target_id is None:
            r = conn.execute(
                "SELECT id FROM submissions WHERE filename LIKE ? "
                "ORDER BY submitted_at DESC LIMIT 1",
                (f"{slot}_%",),
            ).fetchone()
            if r:
                target_id = r[0]

        if target_id is None:
            print(f"  {slot}: NO MATCH (queued; will retry next run)")
            continue

        # Update only if the score is not yet set
        existing = conn.execute(
            "SELECT mathematical_content_score, lane FROM submissions WHERE id = ?",
            (target_id,),
        ).fetchone()
        cur_mcs, cur_lane = existing
        if cur_mcs is not None and cur_lane and cur_lane != "bare":
            print(f"  {slot}: already scored (id={target_id} mcs={cur_mcs} lane={cur_lane})")
            conn.execute(
                "UPDATE mcs_pending_backfill SET applied_at = CURRENT_TIMESTAMP "
                "WHERE slot = ?",
                (slot,),
            )
            applied_count += 1
            continue

        # Apply update (additive; do not clobber lane='bare' if a real one
        # was previously set)
        sets, vals = [], []
        if cur_mcs is None:
            sets.append("mathematical_content_score = ?")
            vals.append(mcs)
        if (cur_lane is None or cur_lane == "bare") and lane != "bare":
            sets.append("lane = ?")
            vals.append(lane)
        if not sets:
            print(f"  {slot}: nothing to update (id={target_id})")
        else:
            vals.append(target_id)
            conn.execute(
                f"UPDATE submissions SET {', '.join(sets)} WHERE id = ?",
                vals,
            )
            print(f"  {slot}: APPLIED id={target_id} mcs={mcs} lane={lane}")

        conn.execute(
            "UPDATE mcs_pending_backfill SET applied_at = CURRENT_TIMESTAMP "
            "WHERE slot = ?",
            (slot,),
        )
        applied_count += 1

    return applied_count


def queue_verdicts(conn):
    """Idempotent insert of S4 verdicts into mcs_pending_backfill."""
    queued = 0
    for slot, (mcs, note) in S4_VERDICTS.items():
        cur = conn.execute(
            "INSERT OR IGNORE INTO mcs_pending_backfill "
            "(slot, mathematical_content_score, note, lane) "
            "VALUES (?, ?, ?, ?)",
            (slot, mcs, note, "bare"),
        )
        if cur.rowcount:
            queued += 1

    for slot, info in NEW_BATCH.items():
        cur = conn.execute(
            "INSERT OR IGNORE INTO mcs_pending_backfill "
            "(slot, uuid, filename, problem_id, lane, "
            " mathematical_content_score, note) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (slot, info["uuid"], info["filename"], info["problem_id"],
             info["lane"], info["mcs"], info["mcs_note"]),
        )
        if cur.rowcount:
            queued += 1

    return queued


def main():
    if not DB_PATH.exists():
        print(f"ERROR: tracking.db not found at {DB_PATH}", file=sys.stderr)
        return 1

    conn = sqlite3.connect(str(DB_PATH))
    try:
        ensure_pending_table(conn)
        queued = queue_verdicts(conn)
        print(f"queued {queued} new verdict(s) into mcs_pending_backfill")
        applied = apply_pending(conn)
        print(f"applied {applied} pending verdict(s) to submissions")
        conn.commit()
    finally:
        conn.close()

    return 0


if __name__ == "__main__":
    sys.exit(main())
