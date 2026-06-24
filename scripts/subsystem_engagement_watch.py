#!/usr/bin/env python3
"""
subsystem_engagement_watch.py
=============================

Polls Aristotle for the 6 inflight informal-mode/fusion submissions
(May 30 2026 wave), and when each one COMPLETES:

  1. Fetches the artifact tarball.
  2. Extracts it into submissions/nu4_final/<slot_or_inflight_label>_extracted/.
  3. Runs the subsystem_engagement_classifier against it.
  4. Appends a structured entry to analysis/inflight_subsystem_audit.md.

When the comparison becomes DECISIVE (>= 3 informal-mode submissions confirm
"informal_reasoner"), prints a clear "DECISIVE" line to stdout that downstream
tooling can pick up as a notification trigger.

Start command (do NOT auto-start — the user controls when this runs):

    nohup python3 scripts/subsystem_engagement_watch.py \\
        --poll-interval 300 \\
        > logs/subsystem_watch.log 2>&1 &

Then tail logs/subsystem_watch.log to monitor.

Inflight UUIDs (from tracking.db rows 1259, 1262, 1263, 1265, plus E100, E373):

    e561c214-eb4c-42a1-87ea-7b49ea0439c2  erdos_938   informal
    4f5fd762-c61c-4c59-a5b1-cf60e4eea7b4  erdos_267   informal
    4697679f-3c66-4f46-a156-7f9900dfdf22  erdos_1003  fusion
    a9e232a2-2593-4765-920a-a3c080a6898d  erdos_1052  informal
    4483a77d-e6db-4f57-bf99-9d9e907cd327  erdos_100   closure   (slot 753 / id 1261)
    67d9e1d9-e73f-4f49-8d4b-60cb8c2fa40e  erdos_373   closure   (id 1260)
"""

from __future__ import annotations

import argparse
import asyncio
import datetime as dt
import json
import os
import sqlite3
import sys
import tarfile
import time
from dataclasses import asdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from subsystem_engagement_classifier import classify_artifact  # noqa: E402

try:
    import aristotlelib
    from aristotlelib import Project, TaskStatus
except ImportError:
    print("ERROR: aristotlelib not installed.", file=sys.stderr)
    sys.exit(1)


NU4_DIR = REPO_ROOT / "submissions" / "nu4_final"
DB_PATH = REPO_ROOT / "submissions" / "tracking.db"
AUDIT_MD = REPO_ROOT / "analysis" / "inflight_subsystem_audit.md"


# The 6 inflight submissions (UUID + label + problem_id + lane).
INFLIGHT: list[dict] = [
    {"uuid": "e561c214-eb4c-42a1-87ea-7b49ea0439c2", "label": "inflight_e938",
     "problem_id": "erdos_938", "lane": "informal"},
    {"uuid": "4f5fd762-c61c-4c59-a5b1-cf60e4eea7b4", "label": "inflight_e267",
     "problem_id": "erdos_267", "lane": "informal"},
    {"uuid": "4697679f-3c66-4f46-a156-7f9900dfdf22", "label": "inflight_e1003",
     "problem_id": "erdos_1003", "lane": "fusion"},
    {"uuid": "a9e232a2-2593-4765-920a-a3c080a6898d", "label": "inflight_e1052",
     "problem_id": "erdos_1052", "lane": "informal"},
    {"uuid": "4483a77d-e6db-4f57-bf99-9d9e907cd327", "label": "inflight_e100",
     "problem_id": "erdos_100", "lane": "closure"},
    {"uuid": "67d9e1d9-e73f-4f49-8d4b-60cb8c2fa40e", "label": "inflight_e373",
     "problem_id": "erdos_373", "lane": "closure"},
]


def get_api_key() -> str:
    key = os.environ.get("ARISTOTLE_API_KEY", "")
    if not key:
        print("ERROR: ARISTOTLE_API_KEY not set in environment.", file=sys.stderr)
        sys.exit(1)
    return key


def utcnow() -> str:
    return dt.datetime.utcnow().isoformat(timespec="seconds") + "Z"


async def task_status_for(uuid: str) -> dict:
    """Return (status_name, percent, file_name) for the most recent task."""
    try:
        p = await Project.from_id(uuid)
        tasks, _ = await p.get_tasks(limit=1)
        if not tasks:
            return {"status": "UNKNOWN", "percent": None, "file_name": None,
                    "error": "no tasks"}
        t = tasks[0]
        return {
            "status": t.status.name,
            "percent": t.percent_complete,
            "file_name": t.file_name,
            "error": None,
        }
    except Exception as e:
        return {"status": "ERROR", "percent": None, "file_name": None, "error": str(e)}


async def fetch_artifact(uuid: str, dest_tar: Path) -> Path | None:
    """Download and return the tarball path; returns None on failure."""
    try:
        p = await Project.from_id(uuid)
        tasks, _ = await p.get_tasks(limit=1)
        if not tasks:
            return None
        t = tasks[0]
        if t.status not in (TaskStatus.COMPLETE, TaskStatus.COMPLETE_WITH_ERRORS):
            return None
        # get_files writes to destination; for a single project this returns
        # the path of the tarball or extracted dir.
        result_path = await p.get_files(destination=str(dest_tar.parent))
        return Path(result_path) if result_path else None
    except Exception as e:
        print(f"  ERROR fetching {uuid}: {e}", file=sys.stderr)
        return None


def extract_tarball(tar_path: Path, dest_dir: Path) -> Path:
    """Extract tar to dest_dir; return dest_dir."""
    dest_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(tar_path, "r:*") as tf:
        # Python 3.12+ requires explicit filter for safe extraction.
        try:
            tf.extractall(path=dest_dir, filter="data")
        except TypeError:
            tf.extractall(path=dest_dir)  # older Pythons
    return dest_dir


def append_audit_entry(entry: dict) -> None:
    """Append a markdown-formatted entry to analysis/inflight_subsystem_audit.md."""
    AUDIT_MD.parent.mkdir(parents=True, exist_ok=True)
    if not AUDIT_MD.exists():
        AUDIT_MD.write_text(
            "# Inflight Subsystem Engagement Audit (S10)\n\n"
            "Auto-populated by `scripts/subsystem_engagement_watch.py`. Each\n"
            "row records the subsystem classification of one inflight\n"
            "informal-mode/fusion/closure submission once it completes.\n\n",
            encoding="utf-8",
        )
    block = (
        f"## {entry['label']} ({entry['problem_id']}, lane={entry['lane']})\n\n"
        f"- **UUID:** `{entry['uuid']}`\n"
        f"- **Completed at:** {entry['completed_at']}\n"
        f"- **Subsystem engaged:** `{entry['subsystem_engaged']}`\n"
        f"- **Validation criteria hit:** {entry['validation_criteria_hit']}\n"
        f"- **Evidence signals:** {entry['evidence_signals']}\n"
        f"- **Artifact:** `{entry['artifact_dir']}`\n\n"
    )
    with AUDIT_MD.open("a", encoding="utf-8") as f:
        f.write(block)


def update_db_completion(uuid: str, classification: str) -> None:
    """Tag the submission row with the subsystem classification (notes column)."""
    try:
        con = sqlite3.connect(DB_PATH)
        con.execute(
            "UPDATE submissions SET notes = COALESCE(notes,'') || ? WHERE uuid = ?",
            (f"\nsubsystem_engaged={classification}", uuid),
        )
        con.commit()
        con.close()
    except Exception as e:
        print(f"  WARN: DB update failed for {uuid}: {e}", file=sys.stderr)


async def process_completed(item: dict) -> dict | None:
    """Fetch + extract + classify one completed submission. Returns the
    classification dict or None on failure."""
    uuid = item["uuid"]
    label = item["label"]
    extract_root = NU4_DIR / f"{label}_extracted"
    if (extract_root / "ARISTOTLE_SUMMARY.md").exists() or any(
        (extract_root / d).is_dir() and (extract_root / d / "ARISTOTLE_SUMMARY.md").exists()
        for d in (extract_root.iterdir() if extract_root.exists() else [])
    ):
        print(f"  Already extracted: {extract_root}")
    else:
        # Download.
        extract_root.mkdir(parents=True, exist_ok=True)
        tar_path = await fetch_artifact(uuid, extract_root / f"{label}.tar.gz")
        if tar_path is None:
            print(f"  Could not fetch {uuid}")
            return None
        # If get_files returned an extracted directory already, that's fine.
        if tar_path.is_dir():
            print(f"  Fetched to dir {tar_path}")
            # Re-point extract_root if needed.
            if tar_path != extract_root:
                extract_root = tar_path.parent
        else:
            print(f"  Extracting {tar_path}")
            try:
                extract_tarball(tar_path, extract_root)
            except Exception as e:
                print(f"  ERROR extracting {tar_path}: {e}", file=sys.stderr)
                return None

    # Classify.
    try:
        result = classify_artifact(extract_root)
    except Exception as e:
        print(f"  ERROR classifying {extract_root}: {e}", file=sys.stderr)
        return None

    entry = {
        "label": label,
        "uuid": uuid,
        "problem_id": item["problem_id"],
        "lane": item["lane"],
        "completed_at": utcnow(),
        "subsystem_engaged": result.subsystem_engaged,
        "validation_criteria_hit": ", ".join(result.validation_criteria_hit) or "(none)",
        "evidence_signals": "; ".join(result.evidence_signals) or "(none)",
        "artifact_dir": result.artifact_dir,
    }
    append_audit_entry(entry)
    update_db_completion(uuid, result.subsystem_engaged)
    return entry


async def poll_loop(poll_interval_s: int) -> None:
    aristotlelib.set_api_key(get_api_key())
    seen: dict[str, str] = {}  # uuid -> classification
    informal_confirmed = 0

    print(f"[{utcnow()}] Watch started. Polling every {poll_interval_s}s for "
          f"{len(INFLIGHT)} UUIDs.")
    print(f"[{utcnow()}] Audit file: {AUDIT_MD}")

    while True:
        any_pending = False
        for item in INFLIGHT:
            uuid = item["uuid"]
            if uuid in seen:
                continue
            st = await task_status_for(uuid)
            status = st["status"]
            if status in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
                print(f"[{utcnow()}] {item['label']} ({uuid[:8]}) -> {status}, processing.")
                entry = await process_completed(item)
                if entry is None:
                    continue
                seen[uuid] = entry["subsystem_engaged"]
                if entry["subsystem_engaged"] == "informal_reasoner":
                    informal_confirmed += 1
                    print(
                        f"[{utcnow()}] CLASSIFIED: {item['label']} -> "
                        f"informal_reasoner (criteria={entry['validation_criteria_hit']})."
                    )
                else:
                    print(
                        f"[{utcnow()}] CLASSIFIED: {item['label']} -> "
                        f"{entry['subsystem_engaged']}."
                    )
                if informal_confirmed >= 3:
                    print(
                        f"[{utcnow()}] DECISIVE: {informal_confirmed} informal-mode "
                        f"submissions confirmed subsystem #2 engagement."
                    )
                    # Continue watching but flag decisively.
            elif status in ("IN_PROGRESS", "QUEUED"):
                any_pending = True
                pct = st["percent"]
                pct_s = f"{pct}%" if pct is not None else ""
                print(f"[{utcnow()}] {item['label']} ({uuid[:8]}) {status} {pct_s}")
            elif status in ("FAILED", "CANCELED", "OUT_OF_BUDGET", "ERROR"):
                print(f"[{utcnow()}] {item['label']} ({uuid[:8]}) -> {status} "
                      f"(err: {st.get('error')}). Marking as seen, will not retry.")
                seen[uuid] = f"job_{status.lower()}"
            else:
                print(f"[{utcnow()}] {item['label']} ({uuid[:8]}) status={status}")

        if len(seen) == len(INFLIGHT):
            print(f"[{utcnow()}] All inflight UUIDs resolved. Exiting.")
            break
        if not any_pending:
            print(f"[{utcnow()}] No pending; sleeping {poll_interval_s}s for retry.")
        await asyncio.sleep(poll_interval_s)


def main() -> int:
    p = argparse.ArgumentParser(description="Watch the 6 inflight informal-mode submissions.")
    p.add_argument("--poll-interval", type=int, default=300,
                   help="Poll interval in seconds (default 300 = 5 min).")
    p.add_argument("--once", action="store_true",
                   help="Single pass: check status, process completed, then exit.")
    args = p.parse_args()

    if args.once:
        asyncio.run(_single_pass())
    else:
        asyncio.run(poll_loop(args.poll_interval))
    return 0


async def _single_pass() -> None:
    aristotlelib.set_api_key(get_api_key())
    for item in INFLIGHT:
        st = await task_status_for(item["uuid"])
        print(f"[{utcnow()}] {item['label']} ({item['uuid'][:8]}) "
              f"status={st['status']}, percent={st['percent']}")
        if st["status"] in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
            entry = await process_completed(item)
            if entry:
                print(f"  -> {entry['subsystem_engaged']} "
                      f"(crit={entry['validation_criteria_hit']})")


if __name__ == "__main__":
    sys.exit(main())
