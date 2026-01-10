#!/usr/bin/env python3
"""
Parallel Aristotle Submission Queue Manager.
Keeps 15 slots busy with validated submissions.

Usage:
  python3 submission_queue.py status      # Show current queue status
  python3 submission_queue.py add <file>  # Add file to queue
  python3 submission_queue.py run         # Submit next batch
  python3 submission_queue.py monitor     # Monitor running jobs

Based on 203 submissions analysis showing optimal patterns.
"""

import sys
import json
import sqlite3
import subprocess
from pathlib import Path
from datetime import datetime
from typing import List, Tuple

BASE_PATH = Path(__file__).parent.parent
DB_PATH = BASE_PATH / "submissions" / "tracking.db"
QUEUE_PATH = BASE_PATH / "submissions" / "queue.json"
MAX_CONCURRENT = 15

def get_db():
    """Get database connection."""
    return sqlite3.connect(str(DB_PATH))

def load_queue() -> dict:
    """Load submission queue."""
    if QUEUE_PATH.exists():
        return json.loads(QUEUE_PATH.read_text())
    return {"pending": [], "submitted": [], "completed": []}

def save_queue(queue: dict):
    """Save submission queue."""
    QUEUE_PATH.write_text(json.dumps(queue, indent=2))

def validate_file(filepath: str) -> Tuple[int, List[str]]:
    """Run pre-submission validator."""
    try:
        # Import validator
        sys.path.insert(0, str(BASE_PATH / "scripts"))
        from pre_submit_validator import validate_file as pv_validate
        return pv_validate(filepath)
    except Exception as e:
        return 2, [f"FAIL: Validation error: {e}"]

def get_running_jobs() -> List[dict]:
    """Get currently running Aristotle jobs."""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        SELECT uuid, filename, problem_id, created_at
        FROM submissions
        WHERE status = 'running' OR status = 'pending'
        ORDER BY created_at DESC
    """)
    jobs = cur.fetchall()
    conn.close()
    return [{"uuid": j[0], "filename": j[1], "problem_id": j[2], "created_at": j[3]}
            for j in jobs]

def get_completed_today() -> int:
    """Get count of jobs completed today."""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        SELECT COUNT(*) FROM submissions
        WHERE status = 'completed'
        AND date(created_at) = date('now')
    """)
    count = cur.fetchone()[0]
    conn.close()
    return count

def add_to_queue(filepath: str):
    """Add file to submission queue after validation."""
    path = Path(filepath)
    if not path.exists():
        print(f"File not found: {filepath}")
        return False

    # Validate
    exit_code, messages = validate_file(filepath)
    print("\n".join(messages))

    if exit_code == 2:
        print(f"\nFailed validation. Not adding to queue.")
        return False

    queue = load_queue()

    entry = {
        "filepath": str(path.absolute()),
        "added": datetime.now().isoformat(),
        "validation_code": exit_code,
        "validation_messages": messages,
    }

    queue["pending"].append(entry)
    save_queue(queue)

    print(f"\nAdded to queue: {filepath}")
    print(f"Queue size: {len(queue['pending'])} pending")
    return True

def show_status():
    """Show queue and job status."""
    queue = load_queue()
    running = get_running_jobs()
    completed_today = get_completed_today()

    print("=" * 60)
    print("ARISTOTLE SUBMISSION QUEUE STATUS")
    print("=" * 60)

    print(f"\n📊 TODAY's STATS:")
    print(f"  Completed: {completed_today}")
    print(f"  Running:   {len(running)}")
    print(f"  Available: {MAX_CONCURRENT - len(running)}")

    print(f"\n📋 QUEUE:")
    print(f"  Pending:   {len(queue['pending'])}")
    print(f"  Submitted: {len(queue['submitted'])}")

    if running:
        print(f"\n🔄 RUNNING JOBS:")
        for job in running[:5]:
            uuid = job['uuid'][:8] if job['uuid'] else "pending_"
            print(f"  - {uuid}: {Path(job['filename']).name}")

    if queue["pending"]:
        print(f"\n⏳ PENDING:")
        for entry in queue["pending"][:5]:
            print(f"  - {Path(entry['filepath']).name}")
        if len(queue["pending"]) > 5:
            print(f"    ... and {len(queue['pending']) - 5} more")

def run_submissions():
    """Submit pending files up to MAX_CONCURRENT."""
    queue = load_queue()
    running = get_running_jobs()
    available_slots = MAX_CONCURRENT - len(running)

    if available_slots <= 0:
        print(f"All {MAX_CONCURRENT} slots in use. Wait for jobs to complete.")
        return

    if not queue["pending"]:
        print("Queue empty. Add files with: python3 submission_queue.py add <file>")
        return

    print(f"Submitting up to {available_slots} files...")

    submitted = 0
    while queue["pending"] and submitted < available_slots:
        entry = queue["pending"].pop(0)
        filepath = entry["filepath"]

        if not Path(filepath).exists():
            print(f"  Skipping (not found): {filepath}")
            continue

        # Re-validate before submission
        exit_code, _ = validate_file(filepath)
        if exit_code == 2:
            print(f"  Skipping (failed validation): {filepath}")
            continue

        # Submit to Aristotle
        try:
            result = subprocess.run(
                ["aristotle", "submit", filepath],
                capture_output=True,
                text=True,
                timeout=30
            )

            if "Created project" in result.stdout or result.returncode == 0:
                print(f"  ✓ Submitted: {Path(filepath).name}")
                entry["submitted"] = datetime.now().isoformat()
                queue["submitted"].append(entry)
                submitted += 1
            else:
                print(f"  ✗ Failed: {Path(filepath).name}")
                print(f"    {result.stderr[:200]}")

        except Exception as e:
            print(f"  ✗ Error: {e}")

    save_queue(queue)
    print(f"\nSubmitted {submitted} files. Remaining in queue: {len(queue['pending'])}")

def monitor_jobs():
    """Monitor running Aristotle jobs."""
    running = get_running_jobs()

    if not running:
        print("No running jobs.")
        return

    print(f"Monitoring {len(running)} jobs...\n")

    for job in running:
        uuid = job["uuid"]
        filename = Path(job["filename"]).name

        try:
            result = subprocess.run(
                ["aristotle", "status", uuid],
                capture_output=True,
                text=True,
                timeout=10
            )

            # Parse status
            if "status:" in result.stdout.lower():
                status_line = [l for l in result.stdout.split('\n') if 'status:' in l.lower()]
                percent_line = [l for l in result.stdout.split('\n') if 'percent' in l.lower()]

                status = status_line[0].split(':')[-1].strip() if status_line else "unknown"
                percent = percent_line[0].split(':')[-1].strip() if percent_line else "?"

                print(f"  {uuid[:8]}: {status} ({percent}%) - {filename}")
            else:
                print(f"  {uuid[:8]}: checking... - {filename}")

        except Exception as e:
            print(f"  {uuid[:8]}: error - {e}")

def scan_and_add():
    """Scan for new submission files and add to queue."""
    submissions_dir = BASE_PATH / "submissions" / "nu4_final"

    print(f"Scanning: {submissions_dir}")

    queue = load_queue()
    queued_files = {entry["filepath"] for entry in queue["pending"]}
    submitted_files = {entry["filepath"] for entry in queue["submitted"]}

    added = 0
    for lean_file in submissions_dir.glob("*.lean"):
        filepath = str(lean_file.absolute())

        if filepath in queued_files or filepath in submitted_files:
            continue

        # Quick validation
        exit_code, _ = validate_file(filepath)

        if exit_code < 2:  # PASS or WARN
            entry = {
                "filepath": filepath,
                "added": datetime.now().isoformat(),
                "validation_code": exit_code,
            }
            queue["pending"].append(entry)
            print(f"  + Added: {lean_file.name}")
            added += 1

    save_queue(queue)
    print(f"\nAdded {added} new files. Queue size: {len(queue['pending'])}")

def main():
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python3 submission_queue.py status   # Show queue status")
        print("  python3 submission_queue.py add <f>  # Add file to queue")
        print("  python3 submission_queue.py run      # Submit pending")
        print("  python3 submission_queue.py monitor  # Check running jobs")
        print("  python3 submission_queue.py scan     # Scan for new files")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "status":
        show_status()
    elif cmd == "add" and len(sys.argv) > 2:
        add_to_queue(sys.argv[2])
    elif cmd == "run":
        run_submissions()
    elif cmd == "monitor":
        monitor_jobs()
    elif cmd == "scan":
        scan_and_add()
    else:
        print(f"Unknown command: {cmd}")
        sys.exit(1)

if __name__ == "__main__":
    main()
