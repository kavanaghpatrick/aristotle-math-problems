#!/usr/bin/env python3
"""
Health Check - Verify all agentic system components are working.
"""

import sqlite3
import subprocess
import asyncio
import sys
import os
from pathlib import Path
from datetime import datetime

sys.path.insert(0, str(Path(__file__).parent))
from config import DB_PATH, GROK_API_KEY, RESULTS_DIR, SUBMISSIONS_DIR


class HealthCheck:
    """Verify system health."""

    def __init__(self):
        self.checks = []
        self.passed = 0
        self.failed = 0

    def log(self, check: str, passed: bool, details: str = ""):
        status = "PASS" if passed else "FAIL"
        icon = "[+]" if passed else "[X]"
        self.checks.append((check, passed, details))

        if passed:
            self.passed += 1
        else:
            self.failed += 1

        print(f"{icon} {check}: {status}")
        if details and not passed:
            print(f"    {details}")

    def check_database(self):
        """Verify database is accessible and has required tables."""
        try:
            conn = sqlite3.connect(DB_PATH)
            cursor = conn.cursor()

            required_tables = [
                'submissions', 'submission_queue', 'generator_tasks',
                'validation_results', 'agentic_metrics', 'aristotle_slots',
                'false_lemmas', 'nu4_cases'
            ]

            cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
            existing = {row[0] for row in cursor.fetchall()}

            missing = [t for t in required_tables if t not in existing]

            conn.close()

            if missing:
                self.log("Database tables", False, f"Missing: {missing}")
            else:
                self.log("Database tables", True)

        except Exception as e:
            self.log("Database connection", False, str(e))

    def check_directories(self):
        """Verify required directories exist."""
        required_dirs = [
            SUBMISSIONS_DIR,
            RESULTS_DIR,
            SUBMISSIONS_DIR / "generated",
            SUBMISSIONS_DIR / "gap_filled",
            Path(__file__).parent / "logs"
        ]

        missing = [d for d in required_dirs if not d.exists()]

        if missing:
            self.log("Directories", False, f"Missing: {[str(d) for d in missing]}")
        else:
            self.log("Directories", True)

    def check_aristotle(self):
        """Verify Aristotle CLI is available."""
        try:
            result = subprocess.run(
                ["aristotle", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                self.log("Aristotle CLI", True)
            else:
                self.log("Aristotle CLI", False, result.stderr[:100])
        except FileNotFoundError:
            self.log("Aristotle CLI", False, "Not found in PATH")
        except Exception as e:
            self.log("Aristotle CLI", False, str(e))

    def check_aristotle_api(self):
        """Verify Aristotle API connection."""
        async def test_api():
            try:
                from aristotlelib import Project
                projects = await Project.list_projects()
                return True, f"Found {len(projects)} project batches"
            except Exception as e:
                return False, str(e)

        try:
            passed, details = asyncio.run(test_api())
            self.log("Aristotle API", passed, details)
        except Exception as e:
            self.log("Aristotle API", False, str(e))

    def check_grok_api(self):
        """Verify Grok API key is set."""
        if GROK_API_KEY:
            # Optionally test with a simple query
            self.log("Grok API key", True)
        else:
            self.log("Grok API key", False, "GROK_API_KEY not set")

    def check_queue_depth(self):
        """Check if queue has items ready for submission."""
        try:
            conn = sqlite3.connect(DB_PATH)
            cursor = conn.cursor()

            cursor.execute("""
            SELECT COUNT(*) FROM submission_queue
            WHERE validation_passed = 1 AND submitted_at IS NULL
            """)
            ready = cursor.fetchone()[0]

            cursor.execute("""
            SELECT COUNT(*) FROM submission_queue
            WHERE validation_passed = 0 AND submitted_at IS NULL
            """)
            pending_validation = cursor.fetchone()[0]

            conn.close()

            if ready > 0:
                self.log("Queue depth", True, f"{ready} ready, {pending_validation} pending validation")
            elif pending_validation > 0:
                self.log("Queue depth", True, f"0 ready, {pending_validation} pending validation")
            else:
                self.log("Queue depth", False, "Queue empty - need to run generators")

        except Exception as e:
            self.log("Queue depth", False, str(e))

    def check_slot_tracking(self):
        """Verify slot tracking is initialized."""
        try:
            conn = sqlite3.connect(DB_PATH)
            cursor = conn.cursor()

            cursor.execute("SELECT COUNT(*) FROM aristotle_slots")
            count = cursor.fetchone()[0]
            conn.close()

            if count == 15:
                self.log("Slot tracking", True, "15 slots initialized")
            else:
                self.log("Slot tracking", False, f"Expected 15 slots, found {count}")

        except Exception as e:
            self.log("Slot tracking", False, str(e))

    def check_python_imports(self):
        """Check required Python imports."""
        required = ['sqlite3', 'asyncio', 'json', 'subprocess', 'pathlib']

        try:
            # Check aristotlelib
            import aristotlelib
            required_found = True
        except ImportError:
            self.log("aristotlelib import", False, "Install with: pip install aristotlelib")
            return

        self.log("Python imports", True)

    def run_all(self):
        """Run all health checks."""
        print("=" * 60)
        print("AGENTIC SYSTEM HEALTH CHECK")
        print(f"Time: {datetime.now().isoformat()}")
        print("=" * 60)
        print()

        self.check_database()
        self.check_directories()
        self.check_aristotle()
        self.check_aristotle_api()
        self.check_grok_api()
        self.check_python_imports()
        self.check_queue_depth()
        self.check_slot_tracking()

        print()
        print("=" * 60)
        print(f"Results: {self.passed} passed, {self.failed} failed")
        print("=" * 60)

        if self.failed > 0:
            print("\nTo fix issues, run:")
            print("  python3 agentic/setup.py --all")
            return 1
        else:
            print("\nSystem is ready!")
            print("\nTo start the system:")
            print("  Terminal 1: python3 agentic/orchestrator.py")
            print("  Terminal 2: python3 agentic/monitor/dashboard.py --watch")
            print("  Terminal 3: python3 agentic/validators/pipeline.py --watch")
            print("  Terminal 4: python3 agentic/generators/pool.py --count 30")
            return 0


def main():
    checker = HealthCheck()
    sys.exit(checker.run_all())


if __name__ == "__main__":
    main()
