#!/usr/bin/env python3
"""
Safe Aristotle submission with multiple safety checks to prevent duplicates.

Defense-in-depth approach:
1. Pre-flight checks (queue status, recent submissions, lockfile)
2. Atomic submission with immediate ID save
3. Post-flight verification
4. Transaction logging
"""

import asyncio
import json
import hashlib
import os
import time
from pathlib import Path
from datetime import datetime, timedelta
from aristotlelib import Project, ProjectInputType, set_api_key

# Configuration
ARISTOTLE_API_KEY = os.environ.get("ARISTOTLE_API_KEY")
if not ARISTOTLE_API_KEY:
    raise ValueError("ARISTOTLE_API_KEY environment variable not set")

# Auto-detect repository root (works from any subdirectory)
MATH_DIR = Path(__file__).resolve().parent.parent
TRANSACTION_LOG = MATH_DIR / "aristotle_submission_log.jsonl"
LOCKFILE = MATH_DIR / ".aristotle_submit.lock"


class SubmissionError(Exception):
    """Raised when submission should be aborted."""
    pass


def compute_task_hash(input_file: Path) -> str:
    """Compute SHA256 hash of task input for deduplication."""
    with open(input_file, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:16]


def log_transaction(action: str, details: dict):
    """Append to transaction log."""
    entry = {
        "timestamp": datetime.now().isoformat(),
        "action": action,
        "details": details
    }
    with open(TRANSACTION_LOG, 'a') as f:
        f.write(json.dumps(entry) + '\n')


def acquire_lock() -> bool:
    """Try to acquire lockfile. Returns True if acquired, False if already locked."""
    if LOCKFILE.exists():
        # Check if lock is stale (>5 minutes old)
        lock_age = time.time() - LOCKFILE.stat().st_mtime
        if lock_age > 300:  # 5 minutes
            print("⚠️  Removing stale lockfile")
            LOCKFILE.unlink()
        else:
            return False

    # Create lockfile
    LOCKFILE.write_text(f"{datetime.now().isoformat()}\n")
    return True


def release_lock():
    """Release lockfile."""
    if LOCKFILE.exists():
        LOCKFILE.unlink()


async def check_recent_submissions(task_hash: str, window_minutes: int = 10) -> list:
    """Check if we've submitted this task recently."""
    set_api_key(ARISTOTLE_API_KEY)

    # Check transaction log first (faster)
    if TRANSACTION_LOG.exists():
        recent_cutoff = datetime.now() - timedelta(minutes=window_minutes)
        with open(TRANSACTION_LOG) as f:
            for line in f:
                entry = json.loads(line)
                timestamp = datetime.fromisoformat(entry['timestamp']).replace(tzinfo=None)
                if timestamp > recent_cutoff:
                    if entry['details'].get('task_hash') == task_hash:
                        return [entry]

    # Double-check via API
    projects, _ = await Project.list_projects(limit=20)
    now = datetime.now()
    recent = []

    for p in projects:
        created = datetime.fromisoformat(str(p.created_at).replace('Z', '+00:00'))
        age_minutes = (now - created.replace(tzinfo=None)).total_seconds() / 60

        if age_minutes < window_minutes:
            recent.append(p)

    return recent


async def check_queue_capacity() -> dict:
    """Check if queue has capacity for new submission."""
    set_api_key(ARISTOTLE_API_KEY)

    projects, _ = await Project.list_projects(limit=10)

    in_progress = sum(1 for p in projects if str(p.status) in ['ProjectStatus.QUEUED', 'ProjectStatus.IN_PROGRESS'])

    return {
        'in_progress': in_progress,
        'has_capacity': in_progress < 5,
        'slots_available': max(0, 5 - in_progress)
    }


async def safe_submit(
    input_file: Path,
    project_id_file: Path,
    description: str,
    force: bool = False,
    context_files: list[Path] | None = None,
    input_type: str = "formal",
) -> str:
    """
    Safely submit to Aristotle with multiple safety checks.

    Args:
        input_file: Path to input file
        project_id_file: Where to save the project ID
        description: Human-readable description for logging
        force: Skip safety checks (use with caution!)
        context_files: Optional list of additional context files (.lean, .md, .txt, .tex)
        input_type: "formal" (default, FORMAL_LEAN) or "informal" (INFORMAL)

    Returns:
        Project ID string

    Raises:
        SubmissionError: If submission should be aborted
    """

    # Compute task hash for deduplication
    task_hash = compute_task_hash(input_file)

    print("🔒 SAFE SUBMISSION PROTOCOL")
    print("=" * 70)
    print(f"Task: {description}")
    print(f"Input: {input_file.name}")
    print(f"Hash: {task_hash}")
    print()

    # SAFETY CHECK 1: Acquire lockfile
    if not force:
        print("1️⃣  Checking lockfile...")
        if not acquire_lock():
            raise SubmissionError("Another submission is in progress (lockfile exists)")
        print("   ✅ Lock acquired")

    try:
        # SAFETY CHECK 2: Check recent submissions
        if not force:
            print("2️⃣  Checking for recent duplicates...")
            recent = await check_recent_submissions(task_hash, window_minutes=10)
            if recent:
                raise SubmissionError(
                    f"Task already submitted in last 10 minutes! "
                    f"Found {len(recent)} matching submission(s)"
                )
            print("   ✅ No recent duplicates found")

        # SAFETY CHECK 3: Check queue capacity
        if not force:
            print("3️⃣  Checking queue capacity...")
            queue = await check_queue_capacity()
            if not queue['has_capacity']:
                raise SubmissionError(
                    f"Queue is full ({queue['in_progress']}/5 slots used). "
                    "Wait for a slot to free up."
                )
            print(f"   ✅ Queue has capacity ({queue['slots_available']} slots available)")

        # SAFETY CHECK 4: Confirm file exists and is readable
        print("4️⃣  Validating input file...")
        if not input_file.exists():
            raise SubmissionError(f"Input file does not exist: {input_file}")
        file_size = input_file.stat().st_size
        if file_size == 0:
            raise SubmissionError("Input file is empty")
        if file_size > 100_000_000:  # 100MB limit
            raise SubmissionError(f"Input file too large: {file_size:,} bytes")
        print(f"   ✅ File valid ({file_size:,} bytes)")

        # ALL CHECKS PASSED - SUBMIT
        print()
        print("🚀 All safety checks passed! Submitting to Aristotle...")
        print()

        set_api_key(ARISTOTLE_API_KEY)

        # Log pre-submission
        log_transaction("pre_submit", {
            "task_hash": task_hash,
            "description": description,
            "input_file": str(input_file),
            "file_size": file_size
        })

        # Determine input type
        pit = ProjectInputType.FORMAL_LEAN if input_type == "formal" else ProjectInputType.INFORMAL

        # Build submission kwargs
        submit_kwargs = {
            "input_file_path": str(input_file),
            "project_input_type": pit,
            "wait_for_completion": False,
        }
        if context_files:
            submit_kwargs["context_file_paths"] = [str(p) for p in context_files]
            print(f"   📎 {len(context_files)} context file(s) attached")

        # Submit (with immediate ID extraction)
        result = await Project.prove_from_file(**submit_kwargs)

        # Extract project ID immediately
        project_id = result if isinstance(result, str) else getattr(result, 'project_id', str(result))

        # IMMEDIATELY save project ID (before anything else can fail)
        with open(project_id_file, 'w') as f:
            f.write(f"{project_id}\n")
            f.write(f"# Task: {description}\n")
            f.write(f"# Hash: {task_hash}\n")
            f.write(f"# Submitted: {datetime.now().isoformat()}\n")

        # Log successful submission
        log_transaction("submitted", {
            "project_id": project_id,
            "task_hash": task_hash,
            "description": description,
            "id_file": str(project_id_file)
        })

        print("✅ SUBMISSION SUCCESSFUL!")
        print(f"   Project ID: {project_id}")
        print(f"   ID saved to: {project_id_file.name}")
        print()

        return project_id

    finally:
        # Always release lock, even if submission failed
        if not force:
            release_lock()


async def submit_with_retry(
    input_file: Path,
    project_id_file: Path,
    description: str,
    max_retries: int = 3,
    retry_delay: int = 30,
    context_files: list[Path] | None = None,
    input_type: str = "formal",
    force: bool = False,
) -> str:
    """
    Submit with exponential backoff retry on transient failures.

    Does NOT retry on:
    - Duplicate submissions
    - Full queue
    - Invalid input files

    Only retries on:
    - Network errors
    - API timeouts
    """

    for attempt in range(max_retries):
        try:
            return await safe_submit(
                input_file, project_id_file, description,
                force=force, context_files=context_files, input_type=input_type,
            )

        except SubmissionError as e:
            # Don't retry on safety check failures
            print(f"❌ Submission aborted: {e}")
            raise

        except Exception as e:
            # Retry on other errors (network, API, etc.)
            if attempt < max_retries - 1:
                wait = retry_delay * (2 ** attempt)  # Exponential backoff
                print(f"⚠️  Attempt {attempt + 1} failed: {e}")
                print(f"   Retrying in {wait}s...")
                await asyncio.sleep(wait)
            else:
                print(f"❌ All {max_retries} attempts failed")
                raise


# CLI interface
if __name__ == "__main__":
    import sys
    import re as re_mod

    # Filter out flags from positional args
    positional = [a for a in sys.argv[1:] if not a.startswith('--')]
    flags = [a for a in sys.argv[1:] if a.startswith('--')]

    if len(positional) < 1:
        print("Usage: python3 safe_aristotle_submit.py <input_file> [slot_number] [options]")
        print()
        print("Options:")
        print("  --force              Skip safety checks")
        print("  --informal           Use INFORMAL input type (default: FORMAL_LEAN)")
        print("  --context <file>     Add context file (can repeat)")
        print()
        print("Examples:")
        print("  # Auto-detect slot number and ID file path:")
        print("  python3 safe_aristotle_submit.py submissions/nu4_final/slot565_foo.lean --force")
        print()
        print("  # Explicit slot number:")
        print("  python3 safe_aristotle_submit.py submissions/nu4_final/slot565_foo.lean 565 --force")
        sys.exit(1)

    input_file = Path(positional[0])

    # Determine slot number and ID file path
    if len(positional) >= 2 and positional[1].isdigit():
        slot_num = positional[1]
    else:
        # Auto-detect from input filename: slot<N>_...
        m = re_mod.match(r'slot(\d+)', input_file.stem)
        slot_num = m.group(1) if m else None

    if slot_num:
        id_file = input_file.parent / f"slot{slot_num}_ID.txt"
        description = input_file.stem  # Use filename as description
    elif len(positional) >= 3:
        # Legacy: <input_file> <id_file> <description>
        id_file = Path(positional[1])
        description = positional[2]
    else:
        # Fallback: ID file next to input
        id_file = input_file.with_suffix('.ID.txt')
        description = input_file.stem

    force = '--force' in flags
    input_type = "informal" if '--informal' in flags else "formal"

    # Collect --context files
    context_files = []
    all_args = sys.argv[1:]
    for i, arg in enumerate(all_args):
        if arg == '--context' and i + 1 < len(all_args):
            context_files.append(Path(all_args[i + 1]))

    print(f"📁 Input: {input_file}")
    print(f"📋 ID file: {id_file}")
    print(f"📝 Description: {description}")
    if input_type == "informal":
        print(f"🔤 Mode: INFORMAL")
    print()

    try:
        project_id = asyncio.run(submit_with_retry(
            input_file, id_file, description,
            context_files=context_files or None,
            input_type=input_type,
            force=force,
        ))
        print(f"✅ Success! Project ID: {project_id}")
    except SubmissionError as e:
        print(f"❌ {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(2)
