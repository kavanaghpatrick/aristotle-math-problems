#!/usr/bin/env python3
"""
Aristotle Queue Manager v2
Monitors the queue and submits files when slots become available.
Includes deduplication to avoid resubmitting files.

Usage:
    python3 scripts/aristotle_queue.py submissions/file1.lean submissions/file2.lean
    python3 scripts/aristotle_queue.py --pending
    python3 scripts/aristotle_queue.py --status  # Check current queue status
"""

import subprocess
import sys
import time
import json
import asyncio
import argparse
from pathlib import Path
from datetime import datetime

# Default files to submit when --pending is used
# NOTE: These are NEW files not yet submitted
PENDING_FILES = [
    # PRIORITY: Tuza full induction - test reduction lemma approach
    "submissions/tuza_full_induction.lean",
    # Remaining from previous batch
    "submissions/batch_dec14_precise/erdos931_precise.lean",
]

SUBMISSIONS_LOG = "submissions/submitted_projects.json"

def log(msg: str):
    """Print timestamped log message."""
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)

def load_submissions_log() -> dict:
    """Load the local submissions log."""
    try:
        with open(SUBMISSIONS_LOG, 'r') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}

def save_submissions_log(data: dict):
    """Save the local submissions log."""
    with open(SUBMISSIONS_LOG, 'w') as f:
        json.dump(data, f, indent=2, default=str)

async def get_queued_files() -> set:
    """Get set of basenames already queued/running in Aristotle."""
    try:
        from aristotlelib import Project
        projects = await Project.list_projects()

        all_projects = []
        for item in projects:
            if isinstance(item, list):
                all_projects.extend(item)

        queued_files = set()
        active_statuses = {'QUEUED', 'IN_PROGRESS', 'RUNNING', 'NOT_STARTED'}

        for p in all_projects:
            status = str(p.status).split('.')[-1]
            if status in active_statuses and p.file_name:
                # Store basename for consistent matching
                queued_files.add(Path(p.file_name).name)

        return queued_files
    except Exception as e:
        log(f"Warning: Could not fetch queue status: {e}")
        return set()

async def get_queue_status() -> dict:
    """Get detailed queue status."""
    try:
        from aristotlelib import Project
        projects = await Project.list_projects()

        all_projects = []
        for item in projects:
            if isinstance(item, list):
                all_projects.extend(item)

        by_status = {}
        for p in all_projects:
            status = str(p.status).split('.')[-1]
            if status not in by_status:
                by_status[status] = []
            by_status[status].append({
                'id': p.project_id,
                'file': p.file_name,
                'desc': p.description,
                'created': str(p.created_at) if p.created_at else None
            })

        return by_status
    except Exception as e:
        return {'ERROR': [{'desc': str(e)}]}

def submit_file(filepath: str) -> tuple[bool, str, str]:
    """
    Try to submit a file to Aristotle.
    Returns (success, message, project_id).
    """
    try:
        result = subprocess.run(
            ["aristotle", "prove-from-file", filepath, "--no-wait"],
            capture_output=True,
            text=True,
            timeout=60
        )

        output = result.stdout + result.stderr
        project_id = None

        # Extract project ID
        for line in output.split('\n'):
            if 'Created project' in line:
                project_id = line.split()[-1]

        if result.returncode == 0:
            return True, f"Submitted! Project ID: {project_id}", project_id

        if "429" in output or "Too Many Requests" in output or "already have 5 projects" in output:
            return False, "Queue full (5/5)", project_id

        return False, f"Error: {output[:200]}", project_id

    except subprocess.TimeoutExpired:
        return False, "Timeout", None
    except Exception as e:
        return False, f"Exception: {e}", None

def monitor_and_submit(files: list[str], check_interval: int = 30, max_wait: int = 3600):
    """
    Monitor queue and submit files when slots are available.
    """
    # Load existing submissions
    submissions_log = load_submissions_log()

    # Check what's already queued
    log("Checking existing queue...")
    queued_files = asyncio.run(get_queued_files())
    if queued_files:
        log(f"Already queued: {queued_files}")

    # Also get basenames from local log for robust matching
    submitted_basenames = {Path(f).name for f in submissions_log.keys()}

    # Filter out already submitted/queued files
    pending = []
    for f in files:
        basename = Path(f).name
        if basename in queued_files:
            log(f"⏭️  Skipping {basename} (already in queue via API)")
        elif f in submissions_log:
            log(f"⏭️  Skipping {basename} (previously submitted: {submissions_log[f]['project_id'][:8]}...)")
        elif basename in submitted_basenames:
            log(f"⏭️  Skipping {basename} (found in local log by basename)")
        else:
            pending.append(f)

    if not pending:
        log("All files already submitted or queued!")
        return [], files

    submitted = []
    start_time = time.time()

    log(f"\nStarting queue monitor for {len(pending)} new files")
    log(f"Check interval: {check_interval}s, Max wait: {max_wait}s")
    print(flush=True)

    while pending:
        elapsed = time.time() - start_time
        if elapsed > max_wait:
            log(f"Max wait time exceeded. {len(pending)} files not submitted.")
            break

        filepath = pending[0]
        filename = Path(filepath).name

        log(f"Attempting: {filename}")
        success, message, project_id = submit_file(filepath)

        if success:
            log(f"✅ {filename}: {message}")
            submitted.append(filepath)
            pending.pop(0)

            # Record submission
            submissions_log[filepath] = {
                'project_id': project_id,
                'submitted_at': datetime.now().isoformat(),
                'status': 'submitted'
            }
            save_submissions_log(submissions_log)
            print(flush=True)

            # Small delay between successful submissions
            if pending:
                time.sleep(2)
        else:
            log(f"⏳ {filename}: {message}")
            remaining = len(pending)
            log(f"   Waiting {check_interval}s... ({remaining} files pending)")
            time.sleep(check_interval)

    print(flush=True)
    log("=" * 50)
    log(f"Submitted this session: {len(submitted)}")
    for f in submitted:
        log(f"  ✅ {Path(f).name}")

    if pending:
        log(f"Not submitted: {len(pending)}")
        for f in pending:
            log(f"  ❌ {Path(f).name}")

    return submitted, pending

def show_status():
    """Show current queue status."""
    log("Fetching Aristotle queue status...")
    status = asyncio.run(get_queue_status())

    print()
    for state, projects in sorted(status.items()):
        print(f"=== {state} ({len(projects)}) ===")
        for p in projects[:15]:
            fname = p.get('file') or "(no filename)"
            desc = (p.get('desc') or "")[:40]
            pid = p.get('id', '')[:8]
            print(f"  {pid}... | {fname}")
            if desc:
                print(f"           {desc}")
        if len(projects) > 15:
            print(f"  ... and {len(projects) - 15} more")
        print()

    # Show local log
    submissions_log = load_submissions_log()
    if submissions_log:
        print("=== Local Submissions Log ===")
        for f, info in submissions_log.items():
            print(f"  {Path(f).name}: {info.get('project_id', 'unknown')[:8]}... ({info.get('status', 'unknown')})")

def main():
    parser = argparse.ArgumentParser(description="Aristotle Queue Manager v2")
    parser.add_argument("files", nargs="*", help="Files to submit")
    parser.add_argument("--pending", action="store_true",
                        help="Submit default pending files")
    parser.add_argument("--status", action="store_true",
                        help="Show queue status only")
    parser.add_argument("--interval", type=int, default=30,
                        help="Check interval in seconds (default: 30)")
    parser.add_argument("--max-wait", type=int, default=3600,
                        help="Max wait time in seconds (default: 3600)")

    args = parser.parse_args()

    if args.status:
        show_status()
        return

    if args.pending:
        files = PENDING_FILES
    elif args.files:
        files = args.files
    else:
        parser.print_help()
        sys.exit(1)

    # Verify files exist
    for f in files:
        if not Path(f).exists():
            log(f"Error: File not found: {f}")
            sys.exit(1)

    submitted, pending = monitor_and_submit(
        files,
        check_interval=args.interval,
        max_wait=args.max_wait
    )

    sys.exit(0 if not pending else 1)

if __name__ == "__main__":
    main()
