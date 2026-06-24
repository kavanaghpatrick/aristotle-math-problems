#!/usr/bin/env python3
"""
Internal helper: runs subsystem_engagement_classifier.classify_artifact()
against ALL existing extracted artifacts under submissions/nu4_final/, looks
up each UUID's lane in tracking.db, and writes a CSV at
analysis/subsystem_engagement_audit.csv.

This file is not a public CLI — it is the implementation behind step 3 of the
S10 framework. Invoke directly:

    python3 scripts/_subsystem_audit_runner.py
"""
from __future__ import annotations

import csv
import sqlite3
import sys
from dataclasses import asdict
from pathlib import Path

# Allow importing the classifier from the same scripts directory.
SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))
from subsystem_engagement_classifier import classify_artifact, ClassificationResult  # noqa: E402

REPO_ROOT = SCRIPTS_DIR.parent
NU4_DIR = REPO_ROOT / "submissions" / "nu4_final"
DB_PATH = REPO_ROOT / "submissions" / "tracking.db"
OUT_CSV = REPO_ROOT / "analysis" / "subsystem_engagement_audit.csv"


def get_lane_from_db(uuid: str | None, slot_label: str | None = None) -> tuple[str | None, str | None, str | None]:
    """Return (lane, status, filename) for the UUID or slot.

    NOTE: The artifact directory name embeds the TASK uuid, not the PROJECT
    uuid that the DB stores. We therefore prefer UUID lookup but fall back to
    matching by slot prefix in `filename`.
    """
    con = sqlite3.connect(DB_PATH)
    try:
        # Try project UUID first.
        if uuid:
            row = con.execute(
                "SELECT lane, status, filename FROM submissions WHERE uuid = ?",
                (uuid,)
            ).fetchone()
            if row is not None:
                return (row[0], row[1], row[2])
        # Fall back to slot label match (most-recent matching submission).
        if slot_label and slot_label.startswith("slot"):
            row = con.execute(
                "SELECT lane, status, filename FROM submissions "
                "WHERE filename LIKE ? ORDER BY id DESC LIMIT 1",
                (f"{slot_label}%",)
            ).fetchone()
            if row is not None:
                return (row[0], row[1], row[2])
        return (None, None, None)
    finally:
        con.close()


def slot_num_from_dir(d: Path) -> str:
    """Pull slot number from a dir name like 'slot723_extracted' or 'i9_extracted'."""
    name = d.name
    if name.startswith("slot"):
        return name.replace("_extracted", "")
    if name == "i9_extracted":
        return "i9_smoke"
    return name


def main() -> int:
    extracted_dirs = sorted(NU4_DIR.glob("*_extracted"))
    if not extracted_dirs:
        print(f"No *_extracted directories under {NU4_DIR}")
        return 1

    OUT_CSV.parent.mkdir(parents=True, exist_ok=True)

    rows: list[dict] = []
    for d in extracted_dirs:
        try:
            res = classify_artifact(d)
        except Exception as e:
            print(f"  ERROR classifying {d}: {e}", file=sys.stderr)
            continue
        slot_label = slot_num_from_dir(d)
        lane, db_status, filename = get_lane_from_db(res.uuid, slot_label)
        rows.append({
            "slot": slot_label,
            "uuid": res.uuid or "",
            "filename": filename or "",
            "lane_db": lane or "",
            "db_status": db_status or "",
            "subsystem_engaged": res.subsystem_engaged,
            "validation_criteria_hit": "|".join(res.validation_criteria_hit),
            "evidence_signals": "|".join(res.evidence_signals),
            "informal_proof_section": int(res.informal_proof_section_present),
            "separate_formalization_section": int(res.separate_formalization_section_present),
            "nl_reasoning_words": res.nl_reasoning_word_count,
            "mathlib_imports_count": len(res.mathlib_modules_imported),
            "summary_words": res.summary_word_count,
            "pure_computational_tactic": int(res.has_native_decide_only_proof),
            "unresolved_sorry": int(res.has_unresolved_sorry),
        })

    fieldnames = list(rows[0].keys()) if rows else []
    with OUT_CSV.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r)

    # Summary stats.
    counts = {"formalizer_only": 0, "informal_reasoner": 0, "ambiguous": 0}
    for r in rows:
        counts[r["subsystem_engaged"]] = counts.get(r["subsystem_engaged"], 0) + 1

    print(f"Audited {len(rows)} artifact(s). Wrote {OUT_CSV.relative_to(REPO_ROOT)}.")
    print(f"  formalizer_only:    {counts['formalizer_only']}")
    print(f"  informal_reasoner:  {counts['informal_reasoner']}")
    print(f"  ambiguous:          {counts['ambiguous']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
