#!/usr/bin/env python3
"""Historical routing audit (U5, 2026-05-30).

For every row in submissions/tracking.db, decide what U1's
`decide_lane()` would have chosen if the auto-routing rule had existed
when that submission was made.

The retrospective rule:
  - FUSION if a sibling <stem>.fusion.json exists on disk *today*
    (proxy for "the author had authored a strategy dossier"; with the
    I8 gate landing on 2026-05-30, no historical submission carried one)
  - BARE otherwise

Output: /Users/patrickkavanagh/math/analysis/historical_routing_audit.csv

Columns: slot,uuid,problem_id,original_lane,would_be_lane_now,reason
"""
from __future__ import annotations

import csv
import re
import sqlite3
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DB_PATH = REPO_ROOT / "submissions" / "tracking.db"
SKETCH_DIRS = [
    REPO_ROOT / "submissions" / "sketches",
    REPO_ROOT / "submissions" / "nu4_final",
    REPO_ROOT / "submissions",
]
OUTPUT_CSV = Path(__file__).parent / "historical_routing_audit.csv"


def find_companion(filename: str) -> Path | None:
    """Search sketch directories for a sibling .fusion.json for `filename`.

    Logic mirrors safe_aristotle_submit._companion_fusion_path —
    strip suffix, append `.fusion.json`.
    """
    if not filename:
        return None
    stem = Path(filename).stem
    for dir_ in SKETCH_DIRS:
        candidate = dir_ / f"{stem}.fusion.json"
        if candidate.exists():
            return candidate
        # Some sketches embed the slot prefix; try without it.
        m = re.match(r"slot\d+_(.+)", stem)
        if m:
            alt_stem = m.group(1)
            alt = dir_ / f"{alt_stem}.fusion.json"
            if alt.exists():
                return alt
    return None


def extract_slot(filename: str) -> str:
    if not filename:
        return ""
    m = re.match(r"slot(\d+)", filename)
    return m.group(1) if m else ""


def main() -> None:
    if not DB_PATH.exists():
        raise SystemExit(f"DB not found at {DB_PATH}")

    conn = sqlite3.connect(str(DB_PATH))
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT id, uuid, filename, problem_id, lane "
        "FROM submissions ORDER BY id"
    ).fetchall()
    conn.close()

    total = 0
    fusion_count = 0
    bare_count = 0
    routing_changed = 0
    fusion_companion_paths: list[str] = []

    OUTPUT_CSV.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT_CSV.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "slot", "uuid", "problem_id", "original_lane",
            "would_be_lane_now", "reason",
        ])

        for row in rows:
            total += 1
            slot = extract_slot(row["filename"] or "")
            uuid = row["uuid"] or ""
            problem_id = row["problem_id"] or ""
            original_lane = row["lane"] or "(unset)"
            companion = find_companion(row["filename"] or "")

            if companion is not None:
                would_be = "FUSION"
                reason = f"sibling companion: {companion.relative_to(REPO_ROOT)}"
                fusion_count += 1
                fusion_companion_paths.append(str(companion.relative_to(REPO_ROOT)))
            else:
                would_be = "BARE"
                reason = "no companion file found"
                bare_count += 1

            # Routing-changed count: original lane was NOT 'fusion' / 'informal'
            # but would-be lane IS 'FUSION' under U1 auto-routing.
            if would_be == "FUSION" and original_lane not in ("fusion", "informal"):
                routing_changed += 1

            writer.writerow([slot, uuid, problem_id, original_lane, would_be, reason])

    print(f"Historical routing audit complete.")
    print(f"  Total submissions:     {total}")
    print(f"  Would be FUSION:       {fusion_count}")
    print(f"  Would be BARE:         {bare_count}")
    print(f"  Routing would change:  {routing_changed}  "
          f"(original lane was bare/closure but companion exists today)")
    print(f"  Output CSV:            {OUTPUT_CSV}")
    if fusion_companion_paths:
        print(f"  Companion files found:")
        for p in fusion_companion_paths:
            print(f"    - {p}")


if __name__ == "__main__":
    main()
