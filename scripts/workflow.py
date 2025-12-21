#!/usr/bin/env python3
"""
Unified submission workflow CLI.

Commands:
  validate <file>     - Run pre-submission validation
  audit <file>        - Run multi-agent audit (Grok + Gemini)
  submit <file>       - Track + validate + submit to Aristotle
  verify <output>     - Verify Aristotle output
  status              - Show current submission status
  history             - Show submission history

Usage:
  python3 scripts/workflow.py validate submissions/problem.lean
  python3 scripts/workflow.py audit submissions/problem.lean
  python3 scripts/workflow.py submit submissions/problem.lean --problem-id tuza_nu4
  python3 scripts/workflow.py status
"""

import subprocess
import sqlite3
import json
import sys
import os
import uuid as uuid_lib
from pathlib import Path
from datetime import datetime, timedelta

MATH_DIR = Path(__file__).resolve().parent.parent
DB_PATH = MATH_DIR / "submissions" / "tracking.db"
SCRIPTS_DIR = MATH_DIR / "scripts"


def ensure_db():
    """Ensure database exists."""
    if not DB_PATH.exists():
        subprocess.run(["python3", str(SCRIPTS_DIR / "init_tracking_db.py")], cwd=MATH_DIR)


def cmd_validate(filepath: str) -> int:
    """Run pre-submission validation."""
    print("=" * 60)
    print("PRE-SUBMISSION VALIDATION")
    print("=" * 60)

    result = subprocess.run(
        ["./scripts/validate_submission.sh", filepath],
        cwd=MATH_DIR
    )
    return result.returncode


def cmd_audit(filepath: str, submission_uuid: str = None) -> int:
    """Run multi-agent audit."""
    args = ["python3", str(SCRIPTS_DIR / "multi_agent_audit.py"), filepath]
    if submission_uuid:
        args.extend(["--submission-uuid", submission_uuid])

    result = subprocess.run(args, cwd=MATH_DIR)
    return result.returncode


def cmd_submit(filepath: str, problem_id: str = "unknown", pattern: str = "unspecified",
               skip_audit: bool = False) -> int:
    """Full submission workflow: validate -> audit -> track -> submit."""

    print("=" * 60)
    print("SUBMISSION WORKFLOW")
    print("=" * 60)
    print(f"File: {filepath}")
    print(f"Problem ID: {problem_id}")
    print(f"Pattern: {pattern}")
    print()

    # Step 1: Validate
    print("Step 1: Validation")
    print("-" * 40)
    val_result = subprocess.run(
        ["./scripts/validate_submission.sh", filepath],
        cwd=MATH_DIR,
        capture_output=True,
        text=True
    )
    if val_result.returncode != 0:
        print("❌ Validation failed:")
        print(val_result.stdout)
        print(val_result.stderr)
        return 1
    print("✅ Validation passed")

    # Step 2: Multi-agent audit (optional)
    if not skip_audit:
        print()
        print("Step 2: Multi-Agent Audit")
        print("-" * 40)
        audit_result = subprocess.run(
            ["python3", str(SCRIPTS_DIR / "multi_agent_audit.py"), filepath],
            cwd=MATH_DIR,
            capture_output=True,
            text=True
        )
        if audit_result.returncode != 0:
            print("⚠️  Audit found issues:")
            print(audit_result.stdout[-1000:] if len(audit_result.stdout) > 1000 else audit_result.stdout)
            print()
            response = input("Continue anyway? [y/N]: ")
            if response.lower() != 'y':
                print("Aborted.")
                return 1
        else:
            print("✅ Audit passed")
    else:
        print()
        print("Step 2: Audit skipped (--skip-audit)")

    # Step 3: Generate UUID and record
    print()
    print("Step 3: Recording Submission")
    print("-" * 40)

    ensure_db()
    submission_uuid = str(uuid_lib.uuid4())[:8]
    filename = Path(filepath).name

    conn = sqlite3.connect(DB_PATH)
    conn.execute("""
        INSERT INTO submissions (uuid, filename, problem_id, pattern, status, syntax_valid, definition_audit_passed)
        VALUES (?, ?, ?, ?, 'validated', 1, 1)
    """, (submission_uuid, filename, problem_id, pattern))
    conn.commit()
    conn.close()

    print(f"✅ Recorded with UUID: {submission_uuid}")

    # Step 4: Show submission command
    print()
    print("Step 4: Ready to Submit")
    print("-" * 40)
    print("Run this command to submit to Aristotle:")
    print()
    print(f"  aristotle prove-from-file {filepath} --no-wait")
    print()
    print("Then update the database with the Aristotle job ID:")
    print(f"  UPDATE submissions SET submitted_at=datetime('now') WHERE uuid='{submission_uuid}';")
    print()

    return 0


def cmd_verify(output_path: str) -> int:
    """Verify Aristotle output file."""
    result = subprocess.run(
        ["./scripts/verify_output.sh", output_path],
        cwd=MATH_DIR
    )
    return result.returncode


def cmd_status() -> int:
    """Show current submission status."""
    ensure_db()

    print("=" * 60)
    print("SUBMISSION STATUS")
    print("=" * 60)

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    # Active submissions
    print("\nActive Submissions:")
    print("-" * 40)
    rows = conn.execute("""
        SELECT uuid, filename, problem_id, status, submitted_at, pattern
        FROM submissions
        WHERE status IN ('validated', 'submitted', 'running')
        ORDER BY created_at DESC
        LIMIT 10
    """).fetchall()

    if rows:
        for row in rows:
            status_emoji = {'validated': '📋', 'submitted': '🚀', 'running': '⏳'}.get(row['status'], '❓')
            print(f"  {status_emoji} [{row['uuid']}] {row['filename']}")
            print(f"     Problem: {row['problem_id']} | Pattern: {row['pattern']}")
            if row['submitted_at']:
                print(f"     Submitted: {row['submitted_at']}")
    else:
        print("  No active submissions")

    # Recent completions
    print("\nRecent Completions (last 7 days):")
    print("-" * 40)
    rows = conn.execute("""
        SELECT uuid, filename, problem_id, status, verified, sorry_count, proven_count
        FROM submissions
        WHERE status IN ('completed', 'failed')
          AND completed_at > datetime('now', '-7 days')
        ORDER BY completed_at DESC
        LIMIT 10
    """).fetchall()

    if rows:
        for row in rows:
            status_emoji = '✅' if row['verified'] == 1 else ('❌' if row['verified'] == 0 else '❓')
            print(f"  {status_emoji} [{row['uuid']}] {row['filename']}")
            if row['sorry_count'] is not None:
                print(f"     Sorry: {row['sorry_count']} | Proven: {row['proven_count']}")
    else:
        print("  No recent completions")

    # Needs verification
    print("\nNeeds Verification:")
    print("-" * 40)
    rows = conn.execute("""
        SELECT uuid, filename, problem_id, grok_reviewed, gemini_reviewed
        FROM submissions
        WHERE status = 'completed' AND verified IS NULL AND proven_count > 0
        ORDER BY completed_at DESC
        LIMIT 5
    """).fetchall()

    if rows:
        for row in rows:
            grok = '✓' if row['grok_reviewed'] else '○'
            gemini = '✓' if row['gemini_reviewed'] else '○'
            print(f"  [{row['uuid']}] {row['filename']}")
            print(f"     Grok: {grok} | Gemini: {gemini}")
    else:
        print("  None pending")

    conn.close()
    return 0


def cmd_history(limit: int = 20) -> int:
    """Show submission history."""
    ensure_db()

    print("=" * 60)
    print("SUBMISSION HISTORY")
    print("=" * 60)

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    rows = conn.execute("""
        SELECT uuid, filename, problem_id, pattern, status, created_at, verified, sorry_count
        FROM submissions
        ORDER BY created_at DESC
        LIMIT ?
    """, (limit,)).fetchall()

    if rows:
        print(f"{'UUID':<10} {'File':<30} {'Problem':<12} {'Status':<12} {'Verified'}")
        print("-" * 80)
        for row in rows:
            verified = {1: '✅', 0: '❌', None: '—'}.get(row['verified'], '?')
            print(f"{row['uuid']:<10} {row['filename'][:28]:<30} {(row['problem_id'] or '')[:10]:<12} {row['status']:<12} {verified}")
    else:
        print("No submissions found")

    conn.close()
    return 0


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    command = sys.argv[1]

    if command == "validate":
        if len(sys.argv) < 3:
            print("Usage: workflow.py validate <file>")
            sys.exit(1)
        sys.exit(cmd_validate(sys.argv[2]))

    elif command == "audit":
        if len(sys.argv) < 3:
            print("Usage: workflow.py audit <file> [--submission-uuid UUID]")
            sys.exit(1)
        uuid = None
        if "--submission-uuid" in sys.argv:
            idx = sys.argv.index("--submission-uuid")
            uuid = sys.argv[idx + 1] if idx + 1 < len(sys.argv) else None
        sys.exit(cmd_audit(sys.argv[2], uuid))

    elif command == "submit":
        if len(sys.argv) < 3:
            print("Usage: workflow.py submit <file> [--problem-id ID] [--pattern PATTERN] [--skip-audit]")
            sys.exit(1)
        filepath = sys.argv[2]
        problem_id = "unknown"
        pattern = "unspecified"
        skip_audit = "--skip-audit" in sys.argv

        if "--problem-id" in sys.argv:
            idx = sys.argv.index("--problem-id")
            problem_id = sys.argv[idx + 1] if idx + 1 < len(sys.argv) else "unknown"
        if "--pattern" in sys.argv:
            idx = sys.argv.index("--pattern")
            pattern = sys.argv[idx + 1] if idx + 1 < len(sys.argv) else "unspecified"

        sys.exit(cmd_submit(filepath, problem_id, pattern, skip_audit))

    elif command == "verify":
        if len(sys.argv) < 3:
            print("Usage: workflow.py verify <output_file>")
            sys.exit(1)
        sys.exit(cmd_verify(sys.argv[2]))

    elif command == "status":
        sys.exit(cmd_status())

    elif command == "history":
        limit = 20
        if len(sys.argv) > 2:
            try:
                limit = int(sys.argv[2])
            except ValueError:
                pass
        sys.exit(cmd_history(limit))

    else:
        print(f"Unknown command: {command}")
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()
