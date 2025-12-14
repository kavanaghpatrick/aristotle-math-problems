#!/usr/bin/env python3
"""
Aristotle Queue Monitor & Auto-Submitter

Features:
- Monitors project status every N seconds
- Auto-submits queued submissions when slots open
- Downloads completed results automatically
- Logs all activity
- Sends desktop notifications (macOS)

Usage:
    python3 scripts/aristotle_monitor.py [--interval 60] [--once]
"""

import asyncio
import argparse
import os
import sys
import json
from pathlib import Path
from datetime import datetime
from typing import Optional

try:
    from aristotlelib import Project, ProjectInputType, ProjectStatus, set_api_key
except ImportError:
    print("ERROR: aristotlelib not installed. Run: pip install aristotlelib")
    sys.exit(1)

# Configuration
MAX_CONCURRENT = 5  # Aristotle's limit
CHECK_INTERVAL = 60  # seconds
DOWNLOADS_DIR = Path.home() / "Downloads"
LOG_FILE = Path(__file__).parent.parent / "submissions" / "monitor_log.txt"

# Pending submissions queue (priority order)
PENDING_SUBMISSIONS = [
    {
        "file": "submissions/erdos_064_2k_cycles_boris_v3_with_context.txt",
        "desc": "Erdős #64 v3: 2^k cycles (enhanced with GP context)",
        "priority": 1,
    },
    {
        "file": "submissions/erdos_152_sidon_gaps_v2_with_context.txt",
        "desc": "Erdős #152 v2: Sidon gaps (enhanced with prior lemmas)",
        "priority": 2,
    },
]

# Track what we've submitted to avoid duplicates
SUBMITTED_FILE = Path(__file__).parent.parent / "submissions" / "auto_submitted.json"


def log(msg: str, also_print: bool = True):
    """Log message to file and optionally print."""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    log_msg = f"[{timestamp}] {msg}"

    if also_print:
        print(log_msg)

    try:
        with open(LOG_FILE, "a") as f:
            f.write(log_msg + "\n")
    except Exception as e:
        print(f"Warning: Could not write to log: {e}")


def notify(title: str, message: str):
    """Send macOS desktop notification."""
    try:
        os.system(f'''osascript -e 'display notification "{message}" with title "{title}"' ''')
    except:
        pass  # Notifications are optional


def load_submitted() -> set:
    """Load set of already-submitted files."""
    if SUBMITTED_FILE.exists():
        try:
            with open(SUBMITTED_FILE) as f:
                return set(json.load(f))
        except:
            return set()
    return set()


def save_submitted(submitted: set):
    """Save set of submitted files."""
    try:
        with open(SUBMITTED_FILE, "w") as f:
            json.dump(list(submitted), f, indent=2)
    except Exception as e:
        log(f"Warning: Could not save submitted state: {e}")


async def get_queue_status() -> dict:
    """Get current queue status."""
    projects, _ = await Project.list_projects(limit=30)

    status = {
        "in_progress": [],
        "queued": [],
        "complete": [],
        "failed": [],
        "total_active": 0,
    }

    for p in projects:
        s = str(p.status)
        entry = {
            "id": p.project_id,
            "desc": p.description or "N/A",
            "status": s,
        }

        if "IN_PROGRESS" in s:
            status["in_progress"].append(entry)
        elif "QUEUED" in s:
            status["queued"].append(entry)
        elif "COMPLETE" in s:
            status["complete"].append(entry)
        elif "FAILED" in s:
            status["failed"].append(entry)

    status["total_active"] = len(status["in_progress"]) + len(status["queued"])
    return status


async def download_result(project_id: str, desc: str) -> Optional[Path]:
    """Download result for a completed project."""
    try:
        project = await Project.from_id(project_id)
        await project.refresh()

        # Get output content
        if hasattr(project, 'output') and project.output:
            filename = f"{project_id[:12]}-output.lean"
            filepath = DOWNLOADS_DIR / filename

            with open(filepath, 'w') as f:
                f.write(project.output)

            log(f"✅ Downloaded: {filename}")
            return filepath
        else:
            log(f"⚠️  No output available for {project_id[:12]}")
            return None

    except Exception as e:
        log(f"❌ Download failed for {project_id[:12]}: {e}")
        return None


async def submit_pending(submitted: set) -> Optional[str]:
    """Submit next pending problem if slot available. Returns project_id if submitted."""
    for item in PENDING_SUBMISSIONS:
        filepath = Path(item["file"])

        if str(filepath) in submitted:
            continue

        if not filepath.exists():
            log(f"⚠️  File not found: {filepath}")
            continue

        try:
            log(f"📤 Submitting: {item['desc']}")

            project_id = await Project.prove_from_file(
                input_file_path=str(filepath),
                project_input_type=ProjectInputType.INFORMAL,
                wait_for_completion=False
            )

            log(f"✅ Submitted! Project ID: {project_id}")
            notify("Aristotle Submission", f"Submitted: {item['desc'][:30]}...")

            # Save project ID
            id_file = filepath.with_suffix('.auto_project_id.txt')
            with open(id_file, 'w') as f:
                f.write(f"{project_id}\n")
                f.write(f"Submitted: {datetime.now().isoformat()}\n")
                f.write(f"Description: {item['desc']}\n")

            # Mark as submitted
            submitted.add(str(filepath))
            save_submitted(submitted)

            return project_id

        except Exception as e:
            if "5 projects in progress" in str(e):
                log(f"⏳ Queue full, will retry later")
                return None
            else:
                log(f"❌ Submission error: {e}")
                continue

    return None


async def check_for_new_completions(known_complete: set) -> list:
    """Check for newly completed projects."""
    status = await get_queue_status()
    new_completions = []

    for proj in status["complete"]:
        if proj["id"] not in known_complete:
            new_completions.append(proj)
            known_complete.add(proj["id"])

    return new_completions


async def monitor_loop(interval: int, run_once: bool = False):
    """Main monitoring loop."""
    log("=" * 60)
    log("🚀 Aristotle Monitor Started")
    log(f"   Check interval: {interval}s")
    log(f"   Pending submissions: {len(PENDING_SUBMISSIONS)}")
    log("=" * 60)

    # Set API key
    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        log("ERROR: ARISTOTLE_API_KEY not set")
        sys.exit(1)
    set_api_key(api_key)

    # Load state
    submitted = load_submitted()
    known_complete = set()

    # Initial scan to populate known_complete
    status = await get_queue_status()
    for proj in status["complete"]:
        known_complete.add(proj["id"])

    iteration = 0

    while True:
        iteration += 1
        log(f"\n--- Check #{iteration} ---")

        try:
            # Get current status
            status = await get_queue_status()

            active = status["total_active"]
            in_prog = len(status["in_progress"])
            queued = len(status["queued"])
            complete = len(status["complete"])

            log(f"📊 Queue: {in_prog} processing, {queued} queued, {complete} complete")

            # Check for new completions
            new_completions = await check_for_new_completions(known_complete)
            if new_completions:
                log(f"🎉 {len(new_completions)} NEW COMPLETION(S)!")
                for proj in new_completions:
                    desc_short = proj["desc"][:40] + "..." if len(proj["desc"]) > 40 else proj["desc"]
                    log(f"   ✅ {proj['id'][:12]}: {desc_short}")
                    notify("Aristotle Complete!", desc_short)

                    # Auto-download
                    await download_result(proj["id"], proj["desc"])

            # Try to submit pending if slots available
            slots_available = MAX_CONCURRENT - in_prog
            pending_count = len([p for p in PENDING_SUBMISSIONS if str(Path(p["file"])) not in submitted])

            if slots_available > 0 and pending_count > 0:
                log(f"📥 {slots_available} slot(s) available, {pending_count} pending")
                project_id = await submit_pending(submitted)
                if project_id:
                    log(f"   → Submitted to slot")
            elif pending_count == 0:
                log(f"📭 No pending submissions remaining")
            else:
                log(f"⏳ Queue full ({in_prog}/{MAX_CONCURRENT}), waiting...")

            # Show currently processing
            if status["in_progress"]:
                log("🔄 Currently processing:")
                for proj in status["in_progress"][:3]:
                    desc_short = proj["desc"][:45] + "..." if len(proj["desc"]) > 45 else proj["desc"]
                    log(f"   • {desc_short}")
                if len(status["in_progress"]) > 3:
                    log(f"   ... and {len(status['in_progress']) - 3} more")

        except Exception as e:
            log(f"❌ Error during check: {e}")

        if run_once:
            log("\n--- Single check complete ---")
            break

        # Wait for next check
        log(f"⏰ Next check in {interval}s...")
        await asyncio.sleep(interval)


def main():
    parser = argparse.ArgumentParser(description="Aristotle Queue Monitor")
    parser.add_argument("--interval", type=int, default=CHECK_INTERVAL,
                        help=f"Check interval in seconds (default: {CHECK_INTERVAL})")
    parser.add_argument("--once", action="store_true",
                        help="Run single check and exit")
    args = parser.parse_args()

    try:
        asyncio.run(monitor_loop(args.interval, args.once))
    except KeyboardInterrupt:
        log("\n👋 Monitor stopped by user")


if __name__ == "__main__":
    main()
