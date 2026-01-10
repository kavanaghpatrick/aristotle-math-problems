#!/usr/bin/env python3
"""
Orchestrator Daemon - Main control loop for the agentic system.

Responsibilities:
- Keep 15 Aristotle slots busy at all times
- Poll for slot availability and submit from queue
- Trigger learning pipeline on completions
- Spawn generators when queue runs low
"""

import asyncio
import sqlite3
import subprocess
import json
import signal
import sys
from datetime import datetime
from pathlib import Path
from typing import Optional, Dict, List, Any

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent))
from config import (
    DB_PATH, MAX_PARALLEL_SLOTS, POLL_INTERVAL_SECONDS,
    RESULT_CHECK_INTERVAL, MIN_QUEUE_DEPTH, SLOT_ALLOCATION
)

class Orchestrator:
    def __init__(self):
        self.running = True
        self.db_path = DB_PATH
        self.active_slots: Dict[int, Dict] = {}
        self.last_generator_spawn = datetime.now()

        # Set up signal handlers for graceful shutdown
        signal.signal(signal.SIGINT, self._handle_shutdown)
        signal.signal(signal.SIGTERM, self._handle_shutdown)

    def _handle_shutdown(self, signum, frame):
        self.log("Received shutdown signal, cleaning up...")
        self.running = False

    def log(self, msg: str, level: str = "INFO"):
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print(f"[{timestamp}] [{level}] {msg}", flush=True)

    def get_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    async def get_aristotle_status(self) -> Dict[str, List]:
        """Get current Aristotle project status."""
        try:
            from aristotlelib import Project
            projects = await Project.list_projects()

            all_projects = []
            for item in projects:
                if isinstance(item, list):
                    all_projects.extend(item)

            by_status = {
                'QUEUED': [],
                'IN_PROGRESS': [],
                'COMPLETE': [],
                'FAILED': [],
                'ERROR': []
            }

            for p in all_projects:
                status = str(p.status).split('.')[-1]
                if status in by_status:
                    by_status[status].append({
                        'id': p.project_id,
                        'file': p.file_name,
                        'created': str(p.created_at) if p.created_at else None
                    })

            return by_status
        except Exception as e:
            self.log(f"Error fetching Aristotle status: {e}", "ERROR")
            return {}

    def get_available_slot_count(self, status: Dict) -> int:
        """Calculate how many slots are available."""
        in_use = len(status.get('QUEUED', [])) + len(status.get('IN_PROGRESS', []))
        return MAX_PARALLEL_SLOTS - in_use

    def get_next_submission(self) -> Optional[Dict]:
        """Get highest priority validated submission from queue."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT id, file_path, priority, case_name, approach
        FROM submission_queue
        WHERE validation_passed = 1
          AND submitted_at IS NULL
          AND failure_count < 3
        ORDER BY priority DESC, created_at ASC
        LIMIT 1
        """)

        row = cursor.fetchone()
        conn.close()

        if row:
            return dict(row)
        return None

    def submit_file(self, file_path: str) -> tuple[bool, str, Optional[str]]:
        """Submit a file to Aristotle."""
        try:
            result = subprocess.run(
                ["aristotle", "prove-from-file", file_path, "--no-wait"],
                capture_output=True,
                text=True,
                timeout=60
            )

            output = result.stdout + result.stderr
            project_id = None

            for line in output.split('\n'):
                if 'Created project' in line:
                    project_id = line.split()[-1]

            if result.returncode == 0 and project_id:
                return True, "Submitted", project_id

            if "429" in output or "Too Many Requests" in output:
                return False, "Rate limited", None

            if "already have" in output.lower() and "project" in output.lower():
                return False, "Queue full", None

            return False, f"Error: {output[:200]}", None

        except subprocess.TimeoutExpired:
            return False, "Timeout", None
        except Exception as e:
            return False, f"Exception: {e}", None

    def mark_submitted(self, queue_id: int, uuid: str):
        """Mark a queue item as submitted."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        UPDATE submission_queue
        SET submitted_at = datetime('now'),
            aristotle_uuid = ?
        WHERE id = ?
        """, (uuid, queue_id))
        conn.commit()
        conn.close()

    def update_slot(self, slot_id: int, project_uuid: str, file_path: str, case_name: str):
        """Update slot tracking."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        UPDATE aristotle_slots
        SET project_uuid = ?,
            file_path = ?,
            case_name = ?,
            status = 'active',
            assigned_at = datetime('now'),
            last_checked = datetime('now')
        WHERE slot_id = ?
        """, (project_uuid, file_path, case_name, slot_id))
        conn.commit()
        conn.close()

    def find_empty_slot(self) -> Optional[int]:
        """Find an empty slot number."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        SELECT slot_id FROM aristotle_slots
        WHERE status = 'empty'
        ORDER BY slot_id
        LIMIT 1
        """)
        row = cursor.fetchone()
        conn.close()
        return row['slot_id'] if row else None

    def clear_slot(self, slot_id: int):
        """Clear a slot after completion."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        UPDATE aristotle_slots
        SET project_uuid = NULL,
            file_path = NULL,
            case_name = NULL,
            status = 'empty',
            assigned_at = NULL
        WHERE slot_id = ?
        """, (slot_id,))
        conn.commit()
        conn.close()

    async def check_completions(self, status: Dict):
        """Check for completed projects and trigger learning."""
        completed = status.get('COMPLETE', []) + status.get('FAILED', [])

        conn = self.get_db()
        cursor = conn.cursor()

        for project in completed:
            pid = project['id']

            # Check if we're tracking this project
            cursor.execute("""
            SELECT slot_id, file_path, case_name
            FROM aristotle_slots
            WHERE project_uuid = ?
            """, (pid,))
            slot = cursor.fetchone()

            if slot:
                self.log(f"Completion detected: {Path(slot['file_path']).name} (slot {slot['slot_id']})")

                # Trigger learning pipeline (async)
                asyncio.create_task(self.trigger_learning(pid, slot['file_path'], slot['case_name']))

                # Clear the slot
                self.clear_slot(slot['slot_id'])

        conn.close()

    async def trigger_learning(self, project_id: str, file_path: str, case_name: str):
        """Trigger the learning pipeline for a completed project."""
        self.log(f"Triggering learning for {project_id[:8]}...")
        try:
            # Run learning extractor as subprocess
            result = subprocess.run(
                ["python3", str(Path(__file__).parent / "learning" / "extractor.py"),
                 "--project-id", project_id,
                 "--file-path", file_path,
                 "--case-name", case_name or "unknown"],
                capture_output=True,
                text=True,
                timeout=300
            )
            if result.returncode == 0:
                self.log(f"Learning complete for {project_id[:8]}")
            else:
                self.log(f"Learning failed for {project_id[:8]}: {result.stderr[:200]}", "ERROR")
        except Exception as e:
            self.log(f"Learning error: {e}", "ERROR")

    def check_queue_depth(self) -> int:
        """Check current queue depth."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        SELECT COUNT(*) FROM submission_queue
        WHERE validation_passed = 1 AND submitted_at IS NULL
        """)
        count = cursor.fetchone()[0]
        conn.close()
        return count

    async def spawn_generators_if_needed(self):
        """Spawn generator tasks if queue is running low."""
        queue_depth = self.check_queue_depth()

        if queue_depth < MIN_QUEUE_DEPTH:
            # Rate limit spawning
            elapsed = (datetime.now() - self.last_generator_spawn).seconds
            if elapsed > 300:  # Max once per 5 minutes
                self.log(f"Queue depth low ({queue_depth}), spawning generators...")

                # Spawn generator pool
                subprocess.Popen(
                    ["python3", str(Path(__file__).parent / "generators" / "pool.py"),
                     "--count", str(MIN_QUEUE_DEPTH - queue_depth)],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL
                )
                self.last_generator_spawn = datetime.now()

    def record_metric(self, name: str, value: float, tags: str = None):
        """Record a metric for the dashboard."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        INSERT INTO agentic_metrics (metric_name, metric_value, tags)
        VALUES (?, ?, ?)
        """, (name, value, tags))
        conn.commit()
        conn.close()

    async def submission_loop(self):
        """Main loop for submitting to Aristotle."""
        self.log("Starting submission loop...")

        while self.running:
            try:
                # Get Aristotle status
                status = await self.get_aristotle_status()
                available = self.get_available_slot_count(status)

                self.record_metric("slots_available", available)
                self.record_metric("slots_in_use", MAX_PARALLEL_SLOTS - available)

                if available > 0:
                    # Try to submit
                    submission = self.get_next_submission()

                    if submission:
                        file_path = submission['file_path']
                        self.log(f"Submitting: {Path(file_path).name} (priority {submission['priority']})")

                        success, message, uuid = self.submit_file(file_path)

                        if success and uuid:
                            self.mark_submitted(submission['id'], uuid)
                            slot_id = self.find_empty_slot()
                            if slot_id:
                                self.update_slot(slot_id, uuid, file_path, submission['case_name'])
                            self.log(f"Submitted to slot {slot_id}: {uuid[:8]}")
                            self.record_metric("submissions_success", 1)
                        else:
                            self.log(f"Submit failed: {message}", "WARN")
                            self.record_metric("submissions_failed", 1)

                            # If rate limited, wait longer
                            if "limited" in message.lower() or "full" in message.lower():
                                await asyncio.sleep(60)
                    else:
                        self.log("Queue empty, waiting for generators...")
                        await self.spawn_generators_if_needed()

                # Check for completions
                await self.check_completions(status)

            except Exception as e:
                self.log(f"Error in submission loop: {e}", "ERROR")

            await asyncio.sleep(POLL_INTERVAL_SECONDS)

    async def run(self):
        """Main entry point."""
        self.log("=" * 60)
        self.log("AGENTIC THEOREM PROVING ORCHESTRATOR")
        self.log(f"Max slots: {MAX_PARALLEL_SLOTS}")
        self.log(f"Poll interval: {POLL_INTERVAL_SECONDS}s")
        self.log("=" * 60)

        await self.submission_loop()

        self.log("Orchestrator shutdown complete")


def main():
    orchestrator = Orchestrator()
    asyncio.run(orchestrator.run())


if __name__ == "__main__":
    main()
