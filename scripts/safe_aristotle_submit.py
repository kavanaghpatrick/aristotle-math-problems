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
import re
import time
from pathlib import Path
from datetime import datetime, timedelta
from aristotlelib import Project, set_api_key

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


class GapTargetingError(SubmissionError):
    """Raised when a submission fails gap-targeting validation."""
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


def check_duplicate(task_hash: str, window_minutes: int = 10) -> bool:
    """Check local transaction log for duplicate submission. No API call."""
    if not TRANSACTION_LOG.exists():
        return False
    recent_cutoff = datetime.now() - timedelta(minutes=window_minutes)
    with open(TRANSACTION_LOG) as f:
        for line in f:
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            timestamp = datetime.fromisoformat(entry['timestamp']).replace(tzinfo=None)
            if timestamp > recent_cutoff:
                if entry['details'].get('task_hash') == task_hash:
                    return True
    return False


async def check_rate_limit_and_capacity(window_minutes: int = 10) -> dict:
    """Single API call to check both rate limit and queue capacity.

    Returns:
        {
            'recent_count': int,     # submissions in last window_minutes
            'in_progress': int,      # queued + in_progress count
            'has_capacity': bool,    # in_progress < 5
            'slots_available': int,  # max(0, 5 - in_progress)
        }
    """
    set_api_key(ARISTOTLE_API_KEY)
    projects, _ = await Project.list_projects(limit=20)
    now = datetime.now()

    recent_count = 0
    in_progress = 0

    for p in projects:
        # Rate limit: count recent submissions
        created = datetime.fromisoformat(str(p.created_at).replace('Z', '+00:00'))
        age_minutes = (now - created.replace(tzinfo=None)).total_seconds() / 60
        if age_minutes < window_minutes:
            recent_count += 1

        # Capacity: count active jobs
        if str(p.status) in ['ProjectStatus.QUEUED', 'ProjectStatus.IN_PROGRESS']:
            in_progress += 1

    return {
        'recent_count': recent_count,
        'in_progress': in_progress,
        'has_capacity': in_progress < 5,
        'slots_available': max(0, 5 - in_progress),
    }


STRATEGY_PATTERNS = [
    re.compile(r'(?i)^#+\s*(proof\s+strategy|proposed\s+(strategy|approach)|key\s+lemma)'),
    re.compile(r'(?i)^#+\s*(main\s+proof|proof\s+assembly|proof\s+outline)'),
    re.compile(r'(?i)^APPROACH\s+\d'),
    re.compile(r'(?i)^FALLBACK\s+\d'),
    re.compile(r'(?i)^(PRIMARY|SECONDARY):\s'),
    re.compile(r'(?i)^###?\s+Lemma\s+\d'),
    re.compile(r'(?i)^\s*Proposed\s+proof:'),
    re.compile(r'(?i)^=+\s*(PROOF|WHAT TO PROVE|APPROACH)'),
]

FALSIFICATION_PATTERNS = [
    re.compile(r'(?i)\b(falsif|disprove|counterexample|negat)'),
    re.compile(r'(?i)\bis\s+this\s+(true|false|real)'),
    re.compile(r'(?i)\btest\s+(whether|if)'),
]

MAX_SKETCH_LINES = 30
MAX_LEAN_LINES_IN_SKETCH = 5


def check_gap_targeting(input_file: Path) -> dict:
    """Validate that input_file targets an open gap. Hard block, no override.

    Returns:
        {"pass": True, "submission_type": "gap_targeting"|"falsification",
         "gap_statement": str, "line_count": int}

    Raises:
        GapTargetingError with actionable fix message.
    """
    suffix = input_file.suffix.lower()

    # C1: Reject .lean files
    if suffix == '.lean':
        raise GapTargetingError(
            "Gap-targeting requires INFORMAL (.txt). Convert to bare conjecture sketch.\n"
            "  Sketch format: OPEN GAP / English statement / Lean statement / Status\n"
            "  Max 30 lines. No proof strategy."
        )

    # C2: Empty file
    content = input_file.read_text()
    if not content.strip():
        raise GapTargetingError("Sketch is empty. Write the bare conjecture statement.")

    lines = content.splitlines()
    non_blank = [l for l in lines if l.strip() and not l.strip().startswith('---')]

    # C3: Line count
    if len(non_blank) > MAX_SKETCH_LINES:
        raise GapTargetingError(
            f"Sketch has {len(non_blank)} non-blank lines (max {MAX_SKETCH_LINES}).\n"
            "  Strip proof strategy — state only the open gap.\n"
            "  Format: OPEN GAP / English / Lean / Status"
        )

    # Check falsification BEFORE strategy (falsification may look strategy-like)
    is_falsification = any(
        p.search(line) for line in lines for p in FALSIFICATION_PATTERNS
    )

    # C4: Strategy keywords (skip if falsification)
    if not is_falsification:
        for line in lines:
            for pattern in STRATEGY_PATTERNS:
                if pattern.search(line):
                    matched = line.strip()[:60]
                    raise GapTargetingError(
                        f"Sketch contains proof guidance: '{matched}'\n"
                        "  Remove all strategy — let Aristotle find the path.\n"
                        "  Keep only: OPEN GAP / English statement / Lean statement / Status"
                    )

    # C5: Extended Lean code blocks
    lean_indicators = [
        'theorem ', 'def ', 'lemma ', 'import ', ':= by', 'where', '  sorry',
        '| ', 'instance ', 'class ', 'structure '
    ]
    lean_lines = sum(1 for l in lines if any(ind in l for ind in lean_indicators))
    if lean_lines > MAX_LEAN_LINES_IN_SKETCH:
        raise GapTargetingError(
            f"Sketch contains {lean_lines} lines of Lean code (max {MAX_LEAN_LINES_IN_SKETCH}).\n"
            "  Use only 1-3 lines for the formal theorem statement."
        )

    # Extract gap statement (first non-blank, non-comment line)
    gap_statement = ""
    for line in lines:
        stripped = line.strip().lstrip('#').lstrip('-').strip()
        if stripped:
            gap_statement = stripped[:200]
            break

    submission_type = "falsification" if is_falsification else "gap_targeting"

    return {
        "pass": True,
        "submission_type": submission_type,
        "gap_statement": gap_statement,
        "line_count": len(non_blank),
    }


def extract_problem_id(input_file: Path) -> str | None:
    """Extract problem ID from sketch filename or content."""
    import re as re_mod

    # From filename: strip slot prefix and extension
    stem = input_file.stem
    m = re_mod.match(r'slot\d+_(.+?)(?:_v\d+)?$', stem)
    if m:
        problem_id = m.group(1).lower().replace(' ', '_')
        return problem_id[:50] if problem_id else None

    # From content: look for OPEN GAP: line
    try:
        content = input_file.read_text()
        for line in content.splitlines()[:5]:
            m2 = re_mod.match(r'(?i)OPEN\s+GAP:\s*(.+)', line)
            if m2:
                problem_id = m2.group(1).strip().lower()
                problem_id = re_mod.sub(r'[^a-z0-9]+', '_', problem_id)
                return problem_id[:50] if problem_id else None
    except Exception:
        pass

    return None


def gather_context(problem_id: str) -> list[Path]:
    """Find all prior _result.lean files for this problem from tracking.db.

    Returns empty list on any error (missing DB, schema mismatch, sqlite errors).
    """
    import sqlite3

    tracking_db = MATH_DIR / "submissions" / "tracking.db"
    if not tracking_db.exists():
        return []

    try:
        conn = sqlite3.connect(str(tracking_db))
        try:
            # Verify the submissions table has expected columns before querying
            cursor = conn.execute("PRAGMA table_info(submissions)")
            columns = {row[1] for row in cursor.fetchall()}
            required = {'problem_id', 'filename', 'output_file', 'status', 'submitted_at'}
            if not required.issubset(columns):
                conn.close()
                return []

            cursor = conn.execute(
                "SELECT output_file FROM submissions "
                "WHERE (problem_id LIKE ? OR filename LIKE ?) "
                "AND output_file IS NOT NULL "
                "AND status IN ('compiled_clean', 'near_miss', 'completed') "
                "ORDER BY submitted_at DESC",
                (f'%{problem_id}%', f'%{problem_id}%')
            )
            rows = cursor.fetchall()
        finally:
            conn.close()
    except (sqlite3.Error, OSError):
        return []

    if not rows:
        return []

    context_paths = []
    for (filepath,) in rows:
        p = Path(filepath)
        if not p.is_absolute():
            p = MATH_DIR / p
        if p.exists():
            context_paths.append(p)

    return context_paths


async def safe_submit(
    input_file: Path,
    project_id_file: Path,
    description: str,
    force: bool = False,
    context_files: list[Path] | None = None,
    batch: bool = False,
) -> str:
    """
    Safely submit to Aristotle with multiple safety checks.

    Args:
        input_file: Path to input file (.txt sketch)
        project_id_file: Where to save the project ID
        description: Human-readable description for logging
        force: Skip safety checks (use with caution!)
        context_files: Optional list of additional context files (.lean, .md, .txt, .tex)

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

    # GAP-TARGETING GATE (runs before all other checks)
    if force:
        # --force bypasses gap-targeting gate (for informal proof pipeline)
        content = input_file.read_text()
        lines = content.splitlines()
        non_blank = [l for l in lines if l.strip() and not l.strip().startswith('---')]
        gap_statement = ""
        for line in lines:
            stripped = line.strip().lstrip('#').lstrip('-').strip()
            if stripped:
                gap_statement = stripped[:200]
                break
        gap_info = {
            "pass": True,
            "submission_type": "informal_proof",
            "gap_statement": gap_statement,
            "line_count": len(non_blank),
        }
        print("   ⚠️  Gap-targeting gate BYPASSED (--force)")
    else:
        gap_info = check_gap_targeting(input_file)
    print(f"   Gap: {gap_info['gap_statement'][:60]}")
    print(f"   Type: {gap_info['submission_type']}")
    print(f"   Lines: {gap_info['line_count']}")
    print()

    # Auto-context: gather prior results
    problem_id = extract_problem_id(input_file)
    if problem_id:
        auto_context = gather_context(problem_id)
        if auto_context:
            if context_files is None:
                context_files = []
            # Merge auto-context with explicit context (no duplicates)
            existing = set(str(p) for p in context_files)
            for ctx in auto_context:
                if str(ctx) not in existing:
                    context_files.append(ctx)
            print(f"   Auto-context: {len(auto_context)} prior result(s) for '{problem_id}'")

    # SAFETY CHECK 1: Acquire lockfile
    if not force:
        print("1️⃣  Checking lockfile...")
        if not acquire_lock():
            raise SubmissionError("Another submission is in progress (lockfile exists)")
        print("   ✅ Lock acquired")

    try:
        # SAFETY CHECK 2: Check for duplicate (local log only, no API call)
        if not force:
            print("2️⃣  Checking for recent duplicates...")
            if check_duplicate(task_hash, window_minutes=10):
                raise SubmissionError(
                    "Task already submitted in last 10 minutes! "
                    "Found matching hash in transaction log."
                )
            print("   ✅ No recent duplicates found")

        # SAFETY CHECK 3: Check rate limit + queue capacity (single API call)
        if not force and not batch:
            print("3️⃣  Checking rate limit and queue capacity...")
            queue = await check_rate_limit_and_capacity(window_minutes=10)
            if not queue['has_capacity']:
                raise SubmissionError(
                    f"Queue is full ({queue['in_progress']}/5 slots used). "
                    "Wait for a slot to free up."
                )
            print(f"   ✅ Queue has capacity ({queue['slots_available']} slots available)")
        elif batch:
            print("3️⃣  Batch mode: skipping interactive rate-limit check")

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

        # Read sketch content as prompt
        prompt_text = input_file.read_text()

        # If context files exist, bundle them into a tar.gz
        tar_path = None
        if context_files:
            import tarfile
            import tempfile
            tar_path = Path(tempfile.mktemp(suffix='.tar.gz'))
            with tarfile.open(tar_path, 'w:gz') as tar:
                for ctx in context_files:
                    tar.add(ctx, arcname=ctx.name)
            print(f"   📎 {len(context_files)} context file(s) bundled")

        # Submit via new Project.create API
        try:
            project = await Project.create(
                prompt=prompt_text,
                tar_file_path=tar_path,
            )
        finally:
            # Clean up temp tar
            if tar_path and tar_path.exists():
                tar_path.unlink()

        project_id = project.project_id

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
    force: bool = False,
    batch: bool = False,
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
                force=force, context_files=context_files,
                batch=batch,
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

    # Separate flags (--xyz) and flag-arguments (--context <file>) from positional args
    all_args = sys.argv[1:]
    positional = []
    flags = set()
    context_files = []
    i = 0
    while i < len(all_args):
        arg = all_args[i]
        if arg == '--context' and i + 1 < len(all_args):
            context_files.append(Path(all_args[i + 1]))
            i += 2
        elif arg == '--codex-context' and i + 1 < len(all_args):
            codex_problem_id = all_args[i + 1]
            best_path = MATH_DIR / "codex_proofs" / codex_problem_id / "best.lean"
            if best_path.exists():
                context_files.append(best_path.resolve())
                print(f"   Codex context: {best_path}")
            else:
                print(f"WARNING: No Codex best proof found for '{codex_problem_id}'")
            i += 2
        elif arg.startswith('--'):
            flags.add(arg)
            i += 1
        else:
            positional.append(arg)
            i += 1

    batch_mode = '--batch' in flags
    force = '--force' in flags

    if len(positional) < 1:
        print("Usage: python3 safe_aristotle_submit.py <input_file> [slot_number] [options]")
        print("       python3 safe_aristotle_submit.py --batch <file1> <file2> ... [options]")
        print()
        print("Options:")
        print("  --force              Skip safety checks")
        print("  --context <file>     Add context file (can repeat)")
        print("  --codex-context <id> Auto-locate best Codex proof as context")
        print("  --batch              Submit multiple files (skips interactive prompts)")
        print()
        print("Examples:")
        print("  # Single file (auto-detect slot):")
        print("  python3 safe_aristotle_submit.py submissions/sketches/erdos850.txt")
        print()
        print("  # Batch submit:")
        print("  python3 safe_aristotle_submit.py --batch sketch1.txt sketch2.txt")
        sys.exit(1)

    def resolve_file(filepath_str: str) -> tuple[Path, Path, str]:
        """Resolve input file -> (input_path, id_file, description)."""
        input_path = Path(filepath_str)
        m = re_mod.match(r'slot(\d+)', input_path.stem)
        slot_num = m.group(1) if m else None
        if slot_num:
            id_path = input_path.parent / f"slot{slot_num}_ID.txt"
            desc = input_path.stem
        else:
            id_path = input_path.with_suffix('.ID.txt')
            desc = input_path.stem
        return input_path, id_path, desc

    if batch_mode:
        # Batch: all positional args are input files
        input_files = positional
        print(f"📦 BATCH MODE: {len(input_files)} file(s)")
        print()

        succeeded = 0
        failed = 0
        for filepath_str in input_files:
            input_file, id_file, description = resolve_file(filepath_str)
            print(f"{'─' * 70}")
            print(f"📁 Input: {input_file}")
            print(f"📋 ID file: {id_file}")
            print(f"📝 Description: {description}")
            print()

            try:
                project_id = asyncio.run(submit_with_retry(
                    input_file, id_file, description,
                    context_files=context_files or None,
                    force=force,
                    batch=True,
                ))
                print(f"✅ Success! Project ID: {project_id}")
                succeeded += 1
            except SubmissionError as e:
                print(f"❌ {e}")
                failed += 1
            except Exception as e:
                print(f"❌ Unexpected error: {e}")
                failed += 1
            print()

        print(f"{'═' * 70}")
        print(f"Batch complete: {succeeded} succeeded, {failed} failed")

    else:
        # Single file mode (original behavior)
        input_file = Path(positional[0])

        if len(positional) >= 2 and positional[1].isdigit():
            slot_num = positional[1]
        else:
            m = re_mod.match(r'slot(\d+)', input_file.stem)
            slot_num = m.group(1) if m else None

        if slot_num:
            id_file = input_file.parent / f"slot{slot_num}_ID.txt"
            description = input_file.stem
        elif len(positional) >= 3:
            id_file = Path(positional[1])
            description = positional[2]
        else:
            id_file = input_file.with_suffix('.ID.txt')
            description = input_file.stem

        print(f"📁 Input: {input_file}")
        print(f"📋 ID file: {id_file}")
        print(f"📝 Description: {description}")
        print()

        try:
            project_id = asyncio.run(submit_with_retry(
                input_file, id_file, description,
                context_files=context_files or None,
                force=force,
                batch=False,
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
