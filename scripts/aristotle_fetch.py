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
    python3 scripts/aristotle_fetch.py ask <slot|uuid> "<prompt>"
                                                            # Send a follow-up ask to an existing project (2.0+)
                                                            # e.g. after a COMPLETE_WITH_ERRORS, request another attempt

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
    from aristotlelib import Project, TaskStatus
except ImportError:
    print("ERROR: aristotlelib not installed. Run: pip install aristotlelib")
    sys.exit(1)

# The verification gauntlet (G1 lake build + G2 faithfulness + G3 literature +
# G4 promotion) is the EXCLUSIVE writer of target_resolved=1 / compiled_advance.
# It is imported best-effort: if it (or its parallel-built deps) is unavailable,
# update_db falls back to the legacy regex verdict with target_resolved=0
# (fail-closed — never promotes). Import is lazy inside update_db to keep the
# hot status path (cmd_status) free of build-env imports.
_SCRIPTS_DIR = Path(__file__).resolve().parent

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

    # Determine verdict — maps to canonical submissions.status enum (2026-05-28):
    #   submitted | compile_failed | compiled_partial | compiled_no_advance
    #   | compiled_advance | disproven
    # Note: 'compiled_advance' is OPT-IN — set by /fetch's gap-resolution
    # prompt or by audit_proven.py, never automatically from sorry/axiom counts.
    # So a clean compile here lands in compiled_no_advance until proven otherwise.
    if has_load_error and sorry_count > 0:
        verdict = "compile_failed"
    elif has_negation:
        verdict = "disproven"
    elif sorry_count == 0 and axiom_count == 0:
        verdict = "compiled_no_advance"
    else:
        # 1 sorry or 2+ sorry → compiled_partial; legacy buckets near_miss/completed
        # both collapse here.
        verdict = "compiled_partial"

    return {
        "sorry": sorry_count,
        "axioms": axiom_count,
        "negation": has_negation,
        "load_error": has_load_error,
        "declarations": decl_count,
        "lines": len(lines),
        "verdict": verdict,
    }


def _run_gauntlet_verdict(uuid: str, output_file: str, audit: dict,
                          source_conjecture: str | None = None,
                          problem_id: str | None = None) -> dict:
    """Route the fetched artifact through the fail-closed verification gauntlet.

    Returns a dict with at least {verdict, target_resolved, cost_usd,
    mathematical_content_score}. This REPLACES the historical hardcoded
    `target_resolved=0` at the fetch wire: target_resolved/compiled_advance are
    now decided EXCLUSIVELY by verification_gauntlet.run_gauntlet (G1∧G2∧G3).

    Fail-closed contract:
      * If the gauntlet (or its parallel-built deps) is unavailable, OR the
        build env is not requested, we fall back to the legacy regex verdict
        with target_resolved=0 — NEVER promoting.
      * G1 lake build runs only when env GAUNTLET_BUILD=1 (the Method-1 loop
        sets it). Otherwise G1 runs in skip_build mode (machine-check shapes
        only, no promotion) so legacy fetch paths keep their current cost
        profile and never falsely promote.
      * No source_conjecture/problem_id -> G1 + G2-structural only, no advance.
    """
    legacy = {
        "verdict": audit["verdict"],
        "target_resolved": 0,
        "cost_usd": None,
        "mathematical_content_score": None,
        "reasons": ["gauntlet unavailable -> legacy regex verdict (fail-closed)"],
    }
    try:
        if str(_SCRIPTS_DIR) not in sys.path:
            sys.path.insert(0, str(_SCRIPTS_DIR))
        import verification_gauntlet as vg  # lazy
    except Exception as e:
        legacy["reasons"] = [f"gauntlet import failed: {e} -> legacy verdict (fail-closed)"]
        return legacy

    # G1 build only when explicitly requested (Method-1 campaign sets this).
    do_build = os.environ.get("GAUNTLET_BUILD", "0") == "1"
    try:
        res = vg.run_gauntlet(
            uuid=uuid or "",
            lean_path=output_file,
            source_conjecture=source_conjecture,
            problem_id=problem_id,
            skip_build=(not do_build),
        )
        # Defensive: enforce the contract shape + fail-closed default.
        if not isinstance(res, dict) or "verdict" not in res:
            return legacy
        res.setdefault("target_resolved", 0)
        res.setdefault("cost_usd", None)
        res.setdefault("mathematical_content_score", None)
        # When the build was skipped, the gauntlet cannot adjudicate compile
        # status — it returns a fail-closed ceiling (compile_failed) because
        # build_ok is False. That would mislabel the legacy fetch path, which
        # never built. So in skip_build mode we KEEP the caller's regex verdict
        # for `status` and only adopt the gauntlet's (always-0) target_resolved.
        # A genuine disproof is still honored.
        if not do_build and res.get("verdict") != "disproven":
            res["verdict"] = audit["verdict"]
        return res
    except Exception as e:
        legacy["reasons"] = [f"gauntlet raised: {e} -> legacy verdict (fail-closed)"]
        return legacy


def _candidate_source_for(problem_id: str) -> str | None:
    """Resolve the canonical source statement for the gauntlet's G2/G3 from
    candidate_queue (source_path file > statement literal). Mirrors
    method1_loop._source_for. Returns a path string or literal text, or None.
    """
    try:
        db = sqlite3.connect(str(DB_PATH))
        try:
            row = db.execute(
                "SELECT source_path, statement FROM candidate_queue "
                "WHERE problem_id = ?", (problem_id,)).fetchone()
        finally:
            db.close()
    except sqlite3.Error:
        return None
    if not row:
        return None
    sp = (row[0] or "").strip()
    if sp:
        p = Path(sp)
        if not p.is_absolute():
            rp = _SCRIPTS_DIR.parent / sp
            p = rp if rp.exists() else p
        if p.exists():
            return str(p)
    stmt = (row[1] or "").strip()
    return stmt or None


def update_db(slot_num: int, uuid: str, audit: dict, output_file: str, task: str = "",
              source_conjecture: str | None = None, problem_id: str | None = None):
    """Update or insert submission record in DB.

    The verdict + target_resolved are decided by the verification gauntlet
    (verification_gauntlet.run_gauntlet) — NOT the hardcoded `0` this used to
    write. cost_usd and mathematical_content_score are populated from the
    gauntlet when available (G4). Fail-closed: gauntlet unavailable / no source
    -> legacy verdict, target_resolved=0.

    G4 metadata propagation (2026-06-10): the gauntlet can only adjudicate G2
    (faithfulness) + G3 (literature) — and thus ever reach a G4 promotion —
    when it knows WHICH conjecture the artifact targets. Resolve problem_id
    from (caller arg > existing DB row > the 'method1:<pid>' filename
    convention) and source_conjecture from candidate_queue. Row 1345
    (method1:erdos_100_piepmeyer, 0-sorry) was stranded "structural-only,
    never advance" by exactly this gap. The row's problem_id is also
    backfilled below so lane/problem metrics aggregate correctly.
    """
    db = sqlite3.connect(str(DB_PATH))
    # Check if entry exists (also used to self-resolve problem_id).
    row = db.execute(
        "SELECT id, problem_id, filename FROM submissions WHERE uuid=?",
        (uuid,)).fetchone()

    if not problem_id and row and (row[1] or "").strip():
        problem_id = row[1].strip()
    if not problem_id and row:
        m = re.match(r"method1:([a-z0-9_]+)$", (row[2] or "").strip())
        if m:
            problem_id = m.group(1)
    if problem_id and not source_conjecture:
        source_conjecture = _candidate_source_for(problem_id)

    gv = _run_gauntlet_verdict(uuid, output_file, audit,
                               source_conjecture=source_conjecture,
                               problem_id=problem_id)
    verdict = gv["verdict"]
    target_resolved = int(gv.get("target_resolved", 0) or 0)
    cost_usd = gv.get("cost_usd")
    mcs = gv.get("mathematical_content_score")
    verified = 1 if verdict in ("compiled_no_advance", "compiled_advance") else 0

    if row:
        db.execute("""
            UPDATE submissions SET
                status = ?,
                sorry_count = ?,
                proven_count = ?,
                verified = ?,
                target_resolved = ?,
                cost_usd = COALESCE(?, cost_usd),
                mathematical_content_score = COALESCE(?, mathematical_content_score),
                completed_at = datetime('now'),
                output_file = ?,
                problem_id = COALESCE(NULLIF(?, ''), problem_id),
                notes = ?
            WHERE uuid = ?
        """, (
            verdict,
            audit["sorry"],
            audit["declarations"],
            verified,
            target_resolved,  # gauntlet-decided (G4); 0 unless G1∧G2∧G3 pass
            cost_usd,
            mcs,
            output_file,
            (problem_id or "").strip(),  # G4 fix: backfill problem_id
            f"Auto-fetched. {audit['lines']} lines, {audit['sorry']} sorry, {audit['axioms']} axiom. "
            f"Gauntlet: {gv.get('reasons', [''])[-1][:160] if gv.get('reasons') else ''}",
            uuid,
        ))
    else:
        filename = f"slot{slot_num}"
        db.execute("""
            INSERT INTO submissions (filename, uuid, status, sorry_count, proven_count, verified,
                target_resolved, cost_usd, mathematical_content_score,
                completed_at, output_file, frontier_id, notes, submitted_at, problem_id)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, datetime('now'), ?, 'formal_conjectures', ?, datetime('now'), ?)
        """, (
            filename,
            uuid,
            verdict,
            audit["sorry"],
            audit["declarations"],
            verified,
            target_resolved,
            cost_usd,
            mcs,
            output_file,
            f"{task}. {audit['lines']} lines.",
            (problem_id or "").strip() or None,  # G4 fix
        ))

    db.commit()
    db.close()


async def check_status(uuid: str) -> dict:
    """Check a single project's status. Returns dict with status info.

    In aristotlelib 2.0, outcome lives on the latest AgentTask, not the Project
    (Project.status is just RUNNING/IDLE/UNKNOWN now).
    """
    try:
        p = await Project.from_id(uuid)
        tasks, _ = await p.get_tasks(limit=1)
        t = tasks[0] if tasks else None
        return {
            "status": t.status.name if t else "UNKNOWN",
            "percent": t.percent_complete if t else None,
            "file_name": (t.file_name if t else None) or "unknown",
            "error": None,
        }
    except Exception as e:
        return {"status": "ERROR", "percent": None, "file_name": "unknown", "error": str(e)}


async def fetch_result(uuid: str, output_path: Path) -> Path | None:
    """Download a completed result. Returns output path or None."""
    try:
        p = await Project.from_id(uuid)
        tasks, _ = await p.get_tasks(limit=1)
        t = tasks[0] if tasks else None

        # Accept COMPLETE and COMPLETE_WITH_ERRORS — both have downloadable artifacts.
        if t is None or t.status not in (TaskStatus.COMPLETE, TaskStatus.COMPLETE_WITH_ERRORS):
            return None

        result_path = await p.get_files(destination=str(output_path))
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
            emoji = "✅" if verdict in ("COMPILED_NO_ADVANCE", "COMPILED_ADVANCE") else "📝" if verdict == "COMPILED_PARTIAL" else "❌"
            print(f"{slot_num:<6} {emoji} {verdict:<11} {sorry:>5} {task:<50} {uuid[:12]}...")
            complete_fetched.append(slot_num)
            continue

        # Check Aristotle status
        status_info = await check_status(uuid)
        st = status_info["status"]
        pct = status_info["percent"]

        if st in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
            label = "COMPLETE" if st == "COMPLETE" else "COMPLETE_ERR"
            print(f"{slot_num:<6} 📥 {label:<12}  —   {task:<50} {uuid[:12]}...")
            complete_unfetched.append(slot_num)
        elif st in ("IN_PROGRESS", "QUEUED"):
            pct_str = f"{pct}%" if pct is not None else ""
            print(f"{slot_num:<6} ⏳ {st:<11} {pct_str:>5} {task:<50} {uuid[:12]}...")
            active.append(slot_num)
        elif st in ("FAILED", "CANCELED", "OUT_OF_BUDGET"):
            print(f"{slot_num:<6} ⚠️  {st:<12}  —   {task:<50} {uuid[:12]}...")
            errors.append(slot_num)
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
    clean_count = 0

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

        if st not in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
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
            emoji = "✅" if verdict in ("COMPILED_NO_ADVANCE", "COMPILED_ADVANCE") else "📝" if verdict == "COMPILED_PARTIAL" else "⚠️"
            print(f"  {emoji} {verdict}: {audit['sorry']} sorry, {audit['axioms']} axiom, {audit['lines']} lines")

            # Gap-resolution prompt — only on clean compiles (sorry=0, no axioms).
            # If the user confirms the gap was actually resolved, they will
            # manually set target_resolved=1 AND we'd promote status to
            # compiled_advance via the /process-result skill or audit_proven.py.
            if verdict == 'COMPILED_NO_ADVANCE':
                print(f"  ╔══════════════════════════════════════════════════╗")
                print(f"  ║  GAP RESOLUTION: Did this resolve the OPEN GAP? ║")
                print(f"  ║  (Not just compile infrastructure/known math)   ║")
                print(f"  ╠══════════════════════════════════════════════════╣")
                print(f"  ║  If YES: sqlite3 submissions/tracking.db        ║")
                print(f"  ║  \"UPDATE submissions SET target_resolved=1       ║")
                print(f"  ║   WHERE uuid='{uuid}'\"                          ║")
                print(f"  ╚══════════════════════════════════════════════════╝")

            # Update DB
            update_db(slot_num, uuid, audit, str(output_path), task)
            print(f"  DB updated.")

            fetched += 1
            if verdict in ("COMPILED_NO_ADVANCE", "COMPILED_ADVANCE"):
                clean_count += 1
        else:
            print(f"  ❌ Download failed")

        print()

    print(f"Done: {fetched} fetched, {clean_count} compiled clean.")


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

    prompt_text = sketch.read_text()

    # Find context file from previous slot result and bundle as tar
    tar_path = None
    if context_slot:
        context_file = result_exists(context_slot)
        if context_file:
            import tarfile, tempfile
            tar_path = Path(tempfile.mktemp(suffix='.tar.gz'))
            with tarfile.open(tar_path, 'w:gz') as tar:
                tar.add(context_file, arcname=context_file.name)
            print(f"Using context from slot {context_slot}: {context_file}")
        else:
            print(f"WARNING: No result file found for context slot {context_slot}")

    try:
        project = await aristotlelib.Project.create(
            prompt=prompt_text,
            tar_file_path=tar_path,
        )
    finally:
        if tar_path and tar_path.exists():
            tar_path.unlink()

    uuid = project.project_id
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


async def cmd_ask(target: str, prompt: str):
    """Send a follow-up `ask` to an existing project (aristotlelib 2.0+).

    Resolves `target` as a slot number (looked up in ID files) or a UUID directly,
    then calls Project.ask(prompt) to spawn a new AgentTask on the same project.
    Avoids re-uploading inputs and keeps the project's conversation context.
    """
    aristotlelib.set_api_key(get_api_key())

    # Resolve target → uuid
    uuid = target
    slot_num = None
    if '-' not in target:
        try:
            slot_num = int(target)
            slots = load_slot_ids()
            if slot_num not in slots:
                print(f"Slot {slot_num} not found in ID files.")
                return
            uuid = slots[slot_num]['uuid']
        except ValueError:
            print(f"Target '{target}' is neither a UUID nor a slot number.")
            return

    print(f"Project: {uuid}")
    print(f"Prompt:  {prompt[:200]}{'...' if len(prompt) > 200 else ''}")
    project = await Project.from_id(uuid)
    task = await project.ask(prompt)
    print(f"  ✓ New task spawned: {task.agent_task_id}")
    print(f"    Status: {task.status.name}")
    if task.description:
        print(f"    Desc:   {task.description[:100]}")

    # Append note to ID file if we know the slot
    if slot_num is not None:
        id_file = RESULTS_DIR / f"slot{slot_num}_ID.txt"
        if id_file.exists():
            from datetime import datetime, timezone
            ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
            with id_file.open('a') as f:
                f.write(f"# Follow-up task {task.agent_task_id} at {ts}: {prompt[:80]}\n")
            print(f"  Appended to {id_file}")


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
    elif cmd == "ask":
        if len(sys.argv) < 4:
            print("Usage: ask <slot|uuid> \"<follow-up prompt>\"")
            print("Example: ask 692 \"try a different decomposition of the case k=3\"")
            sys.exit(1)
        asyncio.run(cmd_ask(sys.argv[2], " ".join(sys.argv[3:])))
    else:
        print(f"Unknown command: {cmd}")
        print("Use: status | fetch [slot|uuid] | track <slot> <uuid> [task] | resub <slot> <sketch> [context_slot] | ask <slot|uuid> \"<prompt>\"")
        sys.exit(1)


if __name__ == "__main__":
    main()
