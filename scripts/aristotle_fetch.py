#!/usr/bin/env python3
"""
Aristotle Fetch & Status Tool

Usage:
    python3 scripts/aristotle_fetch.py status              # Show all active/complete/queued jobs
    python3 scripts/aristotle_fetch.py fetch                # Fetch ALL completed, unfetched results
    python3 scripts/aristotle_fetch.py fetch 565            # Fetch specific slot
    python3 scripts/aristotle_fetch.py fetch <uuid>         # Fetch specific UUID
    python3 scripts/aristotle_fetch.py track <slot> <uuid>  # Create ID file for a slot
    python3 scripts/aristotle_fetch.py resub <slot> <sketch> [context_slot]
                                                            # Resubmit with context from prior result

Reads UUIDs from:
  1. submissions/nu4_final/slot*_ID.txt files (primary)
  2. submissions/tracking.db (secondary)

Downloads results to submissions/nu4_final/<slotname>_result.lean
Runs basic audit (sorry/axiom count) and updates DB.
"""

import asyncio
import os
import re
import sqlite3
import sys
from pathlib import Path

# Ensure we can import aristotlelib
try:
    import aristotlelib
    from aristotlelib import Project
except ImportError:
    print("ERROR: aristotlelib not installed. Run: pip install aristotlelib")
    sys.exit(1)

RESULTS_DIR = Path("submissions/nu4_final")
DB_PATH = Path("submissions/tracking.db")


def get_api_key():
    key = os.environ.get("ARISTOTLE_API_KEY", "")
    if not key:
        print("ERROR: ARISTOTLE_API_KEY not set")
        sys.exit(1)
    return key


def load_slot_ids() -> dict[int, dict]:
    """Load all slot ID files and return {slot_num: {uuid, task, submitted}}."""
    slots = {}
    for f in sorted(RESULTS_DIR.glob("slot*_ID.txt")):
        # Extract slot number from filename like slot565_ID.txt or slot565_whatever_ID.txt
        # Actually the pattern is: the submit script saves to slot<N>_ID.txt directly
        # But some old ones are like slot542_ID.txt
        match = re.match(r'slot(\d+)', f.stem.replace('_ID', ''))
        if not match:
            continue
        slot_num = int(match.group(1))
        lines = f.read_text().strip().split('\n')
        uuid = lines[0].strip() if lines else None
        task = ""
        submitted = ""
        for line in lines[1:]:
            if line.startswith('# Task:'):
                task = line[7:].strip()
            elif line.startswith('# Submitted:'):
                submitted = line[12:].strip()
        if uuid:
            slots[slot_num] = {"uuid": uuid, "task": task, "submitted": submitted, "id_file": str(f)}
    return slots


def load_submission_files() -> dict[int, str]:
    """Map slot numbers to their original submission files (not _ID, not _result)."""
    files = {}
    for f in sorted(RESULTS_DIR.glob("slot*.lean")):
        if '_result' in f.name or '_aristotle' in f.name:
            continue
        match = re.match(r'slot(\d+)', f.stem)
        if match:
            files[int(match.group(1))] = str(f)
    for f in sorted(RESULTS_DIR.glob("slot*.txt")):
        if '_ID' in f.name:
            continue
        match = re.match(r'slot(\d+)', f.stem)
        if match:
            files[int(match.group(1))] = str(f)
    return files


def result_exists(slot_num: int) -> Path | None:
    """Check if a result file already exists for this slot."""
    # Check exact match first (e.g., slot638_result.lean)
    exact = RESULTS_DIR / f"slot{slot_num}_result.lean"
    if exact.exists():
        return exact
    # Then check with descriptive name (e.g., slot638_erdos364_cube_v2_result.lean)
    for f in RESULTS_DIR.glob(f"slot{slot_num}_*_result.lean"):
        return f
    for f in RESULTS_DIR.glob(f"slot{slot_num}_*_result.*"):
        return f
    return None


def audit_file(path: Path) -> dict:
    """Basic audit of a Lean result file."""
    text = path.read_text()
    lines = text.split('\n')

    # Count sorry (excluding comments)
    sorry_count = 0
    for line in lines:
        # Strip comments
        code = re.sub(r'/-.*?-/', '', line)  # block comments (single line)
        code = re.sub(r'--.*$', '', code)     # line comments
        sorry_count += len(re.findall(r'\bsorry\b', code))

    # Count axioms
    axiom_count = len(re.findall(r'^axiom\s', text, re.MULTILINE))

    # Check for negations
    has_negation = bool(re.search(r'(?:negated|counterexample|The following was negated)', text, re.IGNORECASE))

    # Check for Aristotle load errors
    has_load_error = bool(re.search(r'Aristotle failed to load', text))

    # Count theorem/lemma declarations
    decl_count = len(re.findall(r'^(?:theorem|lemma|def)\s', text, re.MULTILINE))

    # Determine verdict
    if has_load_error and sorry_count > 0:
        verdict = "failed"
    elif sorry_count == 0 and axiom_count == 0 and not has_negation:
        verdict = "compiled_clean"
    elif has_negation:
        verdict = "disproven"
    elif sorry_count == 1:
        verdict = "near_miss"
    else:
        verdict = "completed"

    return {
        "sorry": sorry_count,
        "axioms": axiom_count,
        "negation": has_negation,
        "load_error": has_load_error,
        "declarations": decl_count,
        "lines": len(lines),
        "verdict": verdict,
    }


def update_db(slot_num: int, uuid: str, audit: dict, output_file: str, task: str = ""):
    """Update or insert submission record in DB."""
    db = sqlite3.connect(str(DB_PATH))
    # Check if entry exists
    row = db.execute("SELECT id FROM submissions WHERE uuid=?", (uuid,)).fetchone()

    if row:
        db.execute("""
            UPDATE submissions SET
                status = ?,
                sorry_count = ?,
                proven_count = ?,
                verified = ?,
                target_resolved = ?,
                completed_at = datetime('now'),
                output_file = ?,
                notes = ?
            WHERE uuid = ?
        """, (
            audit["verdict"],
            audit["sorry"],
            audit["declarations"],
            1 if audit["verdict"] == "compiled_clean" else 0,
            0,  # target_resolved: set manually when an open problem is actually resolved
            output_file,
            f"Auto-fetched. {audit['lines']} lines, {audit['sorry']} sorry, {audit['axioms']} axiom.",
            uuid,
        ))
    else:
        filename = f"slot{slot_num}"
        db.execute("""
            INSERT INTO submissions (filename, uuid, status, sorry_count, proven_count, verified,
                target_resolved, completed_at, output_file, frontier_id, notes, submitted_at)
            VALUES (?, ?, ?, ?, ?, ?, 0, datetime('now'), ?, 'formal_conjectures', ?, datetime('now'))
        """, (
            filename,
            uuid,
            audit["verdict"],
            audit["sorry"],
            audit["declarations"],
            1 if audit["verdict"] == "compiled_clean" else 0,
            output_file,
            f"{task}. {audit['lines']} lines.",
        ))

    db.commit()
    db.close()


async def check_status(uuid: str) -> dict:
    """Check a single project's status. Returns dict with status info."""
    try:
        p = await Project.from_id(uuid)
        status_str = p.status.value if hasattr(p.status, 'value') else str(p.status)
        # Normalize: ProjectStatus.COMPLETE -> COMPLETE
        status_str = status_str.replace("ProjectStatus.", "")
        return {
            "status": status_str,
            "percent": p.percent_complete,
            "file_name": p.file_name or "unknown",
            "error": None,
        }
    except Exception as e:
        return {"status": "ERROR", "percent": None, "file_name": "unknown", "error": str(e)}


async def fetch_result(uuid: str, output_path: Path) -> Path | None:
    """Download a completed result. Returns output path or None."""
    try:
        p = await Project.from_id(uuid)
        status_str = p.status.value if hasattr(p.status, 'value') else str(p.status)
        status_str = status_str.replace("ProjectStatus.", "")

        if status_str != "COMPLETE":
            return None

        result_path = await p.get_solution(output_path=str(output_path))
        return Path(result_path) if result_path else output_path
    except Exception as e:
        print(f"  ERROR fetching: {e}")
        return None


async def cmd_status():
    """Show status of all tracked submissions."""
    aristotlelib.set_api_key(get_api_key())
    slots = load_slot_ids()
    sub_files = load_submission_files()

    if not slots:
        print("No slot ID files found.")
        return

    print(f"{'Slot':<6} {'Status':<14} {'Sorry':>5} {'Task':<50} {'UUID':<14}")
    print("=" * 95)

    active = []
    complete_unfetched = []
    complete_fetched = []
    errors = []

    for slot_num in sorted(slots.keys()):
        info = slots[slot_num]
        uuid = info["uuid"]
        task = info["task"][:48] if info["task"] else ""

        # Check if already fetched
        existing_result = result_exists(slot_num)
        if existing_result:
            audit = audit_file(existing_result)
            verdict = audit["verdict"].upper()
            sorry = audit["sorry"]
            emoji = "✅" if verdict == "COMPILED_CLEAN" else "📝" if verdict == "NEAR_MISS" else "❌"
            print(f"{slot_num:<6} {emoji} {verdict:<11} {sorry:>5} {task:<50} {uuid[:12]}...")
            complete_fetched.append(slot_num)
            continue

        # Check Aristotle status
        status_info = await check_status(uuid)
        st = status_info["status"]
        pct = status_info["percent"]

        if st == "COMPLETE":
            print(f"{slot_num:<6} 📥 COMPLETE       —   {task:<50} {uuid[:12]}...")
            complete_unfetched.append(slot_num)
        elif st in ("IN_PROGRESS", "QUEUED", "NOT_STARTED", "PENDING_RETRY"):
            pct_str = f"{pct}%" if pct is not None else ""
            print(f"{slot_num:<6} ⏳ {st:<11} {pct_str:>5} {task:<50} {uuid[:12]}...")
            active.append(slot_num)
        elif st == "ERROR":
            print(f"{slot_num:<6} ⚠️  ERROR          —   {task:<50} {uuid[:12]}...")
            errors.append(slot_num)
        else:
            print(f"{slot_num:<6} ❓ {st:<11}   —   {task:<50} {uuid[:12]}...")

    print()
    print(f"Summary: {len(complete_fetched)} fetched, {len(complete_unfetched)} ready to fetch, {len(active)} active, {len(errors)} errors")

    if complete_unfetched:
        print(f"\n  Ready to fetch: slots {', '.join(str(s) for s in complete_unfetched)}")
        print(f"  Run: python3 scripts/aristotle_fetch.py fetch")


async def cmd_fetch(target: str | None = None):
    """Fetch completed results."""
    aristotlelib.set_api_key(get_api_key())
    slots = load_slot_ids()
    sub_files = load_submission_files()

    if not slots:
        print("No slot ID files found.")
        return

    # Determine which slots to fetch
    if target and target.lower() not in ("all", ""):
        # Specific slot or UUID
        if '-' in target:
            # UUID - find matching slot
            target_slots = {s: info for s, info in slots.items() if info["uuid"] == target}
        else:
            # Slot number
            slot_num = int(target)
            if slot_num in slots:
                target_slots = {slot_num: slots[slot_num]}
            else:
                print(f"Slot {slot_num} not found in ID files.")
                return
    else:
        # All unfetched completions
        target_slots = {}
        for slot_num, info in slots.items():
            if not result_exists(slot_num):
                target_slots[slot_num] = info

    if not target_slots:
        print("Nothing to fetch (all results already downloaded).")
        return

    fetched = 0
    proven = 0

    for slot_num in sorted(target_slots.keys()):
        info = target_slots[slot_num]
        uuid = info["uuid"]
        task = info["task"]

        # Determine output filename
        # Find the original submission file to derive the result name
        sub_file = sub_files.get(slot_num)
        if sub_file:
            base = Path(sub_file).stem
            output_path = RESULTS_DIR / f"{base}_result.lean"
        else:
            output_path = RESULTS_DIR / f"slot{slot_num}_result.lean"

        print(f"[slot{slot_num}] {task}")
        print(f"  UUID: {uuid}")

        # Check status first
        status_info = await check_status(uuid)
        st = status_info["status"]

        if st != "COMPLETE":
            pct = status_info["percent"]
            pct_str = f" ({pct}%)" if pct is not None else ""
            if st == "ERROR":
                print(f"  Status: {st} — {status_info['error']}")
            else:
                print(f"  Status: {st}{pct_str} — skipping")
            print()
            continue

        # Fetch
        print(f"  Downloading → {output_path}")
        result = await fetch_result(uuid, output_path)

        if result and output_path.exists():
            # Audit
            audit = audit_file(output_path)
            verdict = audit["verdict"].upper()
            emoji = "✅" if verdict == "COMPILED_CLEAN" else "📝" if verdict == "NEAR_MISS" else "⚠️"
            print(f"  {emoji} {verdict}: {audit['sorry']} sorry, {audit['axioms']} axiom, {audit['lines']} lines")

            # Update DB
            update_db(slot_num, uuid, audit, str(output_path), task)
            print(f"  DB updated.")

            fetched += 1
            if verdict == "COMPILED_CLEAN":
                proven += 1
        else:
            print(f"  ❌ Download failed")

        print()

    print(f"Done: {fetched} fetched, {proven} compiled clean.")


def cmd_track(slot: int, uuid: str, task: str = ""):
    """Create a properly formatted slot ID file. Prevents filename mangling."""
    id_file = RESULTS_DIR / f"slot{slot}_ID.txt"
    from datetime import datetime, timezone
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
    id_file.write_text(f"{uuid}\n# Task: {task}\n# Submitted: {timestamp}\n")
    print(f"Tracked slot {slot}: {uuid}")
    print(f"  File: {id_file}")


async def cmd_resub(slot: int, sketch_path: str, context_slot: int | None = None):
    """Resubmit a sketch with optional context from a previous result. Creates proper ID file."""
    aristotlelib.set_api_key(get_api_key())

    sketch = Path(sketch_path)
    if not sketch.exists():
        print(f"ERROR: Sketch not found: {sketch}")
        return

    kwargs = {
        "input_file_path": str(sketch),
        "project_input_type": aristotlelib.ProjectInputType.INFORMAL,
        "wait_for_completion": False,
    }

    # Find context file from previous slot result
    if context_slot:
        context_file = result_exists(context_slot)
        if context_file:
            kwargs["context_file_paths"] = [str(context_file)]
            print(f"Using context from slot {context_slot}: {context_file}")
        else:
            print(f"WARNING: No result file found for context slot {context_slot}")

    uuid = await aristotlelib.Project.prove_from_file(**kwargs)
    print(f"Submitted as slot {slot}: {uuid}")

    # Track it properly
    task_desc = f"Resub of {sketch.stem}"
    if context_slot:
        task_desc += f" with context from slot{context_slot}"
    cmd_track(slot, uuid, task_desc)

    # Update DB
    try:
        conn = sqlite3.connect(str(DB_PATH))
        conn.execute(
            "INSERT OR REPLACE INTO submissions (filename, uuid, problem_id, status, frontier_id, notes, submitted_at) "
            "VALUES (?, ?, ?, 'submitted', 'discovery', ?, datetime('now'))",
            (f"slot{slot}_resub.txt", uuid, f"slot{slot}", task_desc),
        )
        conn.commit()
        conn.close()
        print(f"DB updated.")
    except Exception as e:
        print(f"DB update failed: {e}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(0)

    cmd = sys.argv[1].lower()

    if cmd == "status":
        asyncio.run(cmd_status())
    elif cmd == "fetch":
        target = sys.argv[2] if len(sys.argv) > 2 else None
        asyncio.run(cmd_fetch(target))
    elif cmd == "track":
        if len(sys.argv) < 4:
            print("Usage: track <slot> <uuid> [task description]")
            sys.exit(1)
        task = " ".join(sys.argv[4:]) if len(sys.argv) > 4 else ""
        cmd_track(int(sys.argv[2]), sys.argv[3], task)
    elif cmd == "resub":
        if len(sys.argv) < 4:
            print("Usage: resub <new_slot> <sketch_path> [context_slot]")
            print("Example: resub 642 submissions/nu4_final/slot634_erdos364_cube_center_exclusion.txt 638")
            sys.exit(1)
        context = int(sys.argv[4]) if len(sys.argv) > 4 else None
        asyncio.run(cmd_resub(int(sys.argv[2]), sys.argv[3], context))
    else:
        print(f"Unknown command: {cmd}")
        print("Use: status | fetch [slot|uuid] | track <slot> <uuid> [task] | resub <slot> <sketch> [context_slot]")
        sys.exit(1)


if __name__ == "__main__":
    main()
