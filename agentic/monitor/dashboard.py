#!/usr/bin/env python3
"""
Monitor Dashboard - Real-time visibility into the agentic system.

Features:
- Slot status (15 slots)
- Queue depth and composition
- Success/failure rates
- Recent activity log
- Metrics visualization (terminal)
"""

import sqlite3
import asyncio
import argparse
import json
import sys
from pathlib import Path
from datetime import datetime, timedelta
from typing import Dict, List, Optional

sys.path.insert(0, str(Path(__file__).parent.parent))
from config import DB_PATH, MAX_PARALLEL_SLOTS


class Dashboard:
    """Terminal-based monitoring dashboard."""

    def __init__(self):
        self.db_path = DB_PATH

    def get_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    def clear_screen(self):
        print("\033[2J\033[H", end="")

    def get_slot_status(self) -> List[Dict]:
        """Get status of all 15 slots."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT slot_id, project_uuid, file_path, case_name, status, assigned_at
        FROM aristotle_slots
        ORDER BY slot_id
        """)

        slots = [dict(row) for row in cursor.fetchall()]
        conn.close()
        return slots

    def get_queue_stats(self) -> Dict:
        """Get queue statistics."""
        conn = self.get_db()
        cursor = conn.cursor()

        # Total pending
        cursor.execute("""
        SELECT COUNT(*) FROM submission_queue
        WHERE submitted_at IS NULL
        """)
        total_pending = cursor.fetchone()[0]

        # Validated pending
        cursor.execute("""
        SELECT COUNT(*) FROM submission_queue
        WHERE submitted_at IS NULL AND validation_passed = 1
        """)
        validated_pending = cursor.fetchone()[0]

        # By case
        cursor.execute("""
        SELECT case_name, COUNT(*) as count
        FROM submission_queue
        WHERE submitted_at IS NULL AND validation_passed = 1
        GROUP BY case_name
        ORDER BY count DESC
        """)
        by_case = {row['case_name'] or 'unknown': row['count'] for row in cursor.fetchall()}

        # By priority
        cursor.execute("""
        SELECT
            CASE
                WHEN priority >= 80 THEN 'high'
                WHEN priority >= 50 THEN 'medium'
                ELSE 'low'
            END as level,
            COUNT(*) as count
        FROM submission_queue
        WHERE submitted_at IS NULL AND validation_passed = 1
        GROUP BY level
        """)
        by_priority = {row['level']: row['count'] for row in cursor.fetchall()}

        conn.close()

        return {
            'total_pending': total_pending,
            'validated_pending': validated_pending,
            'by_case': by_case,
            'by_priority': by_priority
        }

    def get_recent_completions(self, hours: int = 24) -> List[Dict]:
        """Get recent completed submissions."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT filename, sorry_count, proven_count, completed_at,
               CASE
                   WHEN sorry_count = 0 AND proven_count > 0 THEN 'SUCCESS'
                   WHEN sorry_count BETWEEN 1 AND 2 THEN 'NEAR_MISS'
                   ELSE 'INCOMPLETE'
               END as result
        FROM submissions
        WHERE status = 'completed'
          AND completed_at > datetime('now', '-' || ? || ' hours')
        ORDER BY completed_at DESC
        LIMIT 20
        """, (hours,))

        completions = [dict(row) for row in cursor.fetchall()]
        conn.close()
        return completions

    def get_metrics_summary(self) -> Dict:
        """Get summary metrics."""
        conn = self.get_db()
        cursor = conn.cursor()

        # Last 24h metrics
        cursor.execute("""
        SELECT metric_name, SUM(metric_value) as total, AVG(metric_value) as avg
        FROM agentic_metrics
        WHERE timestamp > datetime('now', '-24 hours')
        GROUP BY metric_name
        """)

        metrics = {}
        for row in cursor.fetchall():
            metrics[row['metric_name']] = {
                'total': row['total'],
                'avg': row['avg']
            }

        # False lemmas count
        cursor.execute("SELECT COUNT(*) FROM false_lemmas")
        metrics['false_lemmas_known'] = {'total': cursor.fetchone()[0]}

        # Proven theorems count
        cursor.execute("SELECT COUNT(*) FROM proven_theorems WHERE proof_complete = 1")
        metrics['proven_theorems'] = {'total': cursor.fetchone()[0]}

        conn.close()
        return metrics

    def render_slots(self, slots: List[Dict]) -> str:
        """Render slot status display."""
        lines = ["=" * 70, "ARISTOTLE SLOTS (15)", "=" * 70]

        for slot in slots:
            slot_id = slot['slot_id']
            status = slot['status']

            if status == 'empty':
                indicator = "[ ]"
                details = "empty"
            else:
                indicator = "[*]"
                case = slot['case_name'] or 'unknown'
                file = Path(slot['file_path']).stem[:20] if slot['file_path'] else 'unknown'
                uuid = slot['project_uuid'][:8] if slot['project_uuid'] else '????????'
                details = f"{case}: {file}... ({uuid})"

            lines.append(f"  Slot {slot_id:2d} {indicator} {details}")

        active = sum(1 for s in slots if s['status'] != 'empty')
        lines.append(f"\n  Active: {active}/{MAX_PARALLEL_SLOTS}")

        return "\n".join(lines)

    def render_queue(self, stats: Dict) -> str:
        """Render queue status display."""
        lines = ["\n" + "=" * 70, "SUBMISSION QUEUE", "=" * 70]

        lines.append(f"  Total Pending: {stats['total_pending']}")
        lines.append(f"  Validated & Ready: {stats['validated_pending']}")

        if stats['by_case']:
            lines.append("\n  By Case:")
            for case, count in stats['by_case'].items():
                bar = "#" * min(count, 20)
                lines.append(f"    {case:15s} [{bar:20s}] {count}")

        if stats['by_priority']:
            lines.append("\n  By Priority:")
            for level, count in stats['by_priority'].items():
                lines.append(f"    {level:10s}: {count}")

        return "\n".join(lines)

    def render_completions(self, completions: List[Dict]) -> str:
        """Render recent completions."""
        lines = ["\n" + "=" * 70, "RECENT COMPLETIONS (24h)", "=" * 70]

        if not completions:
            lines.append("  No recent completions")
        else:
            for c in completions[:10]:
                result = c['result']
                icon = {
                    'SUCCESS': '+',
                    'NEAR_MISS': '~',
                    'INCOMPLETE': '-'
                }.get(result, '?')

                filename = Path(c['filename']).stem[:25] if c['filename'] else 'unknown'
                lines.append(f"  [{icon}] {filename:25s} | proven: {c['proven_count']} | sorry: {c['sorry_count']}")

            # Summary
            success = sum(1 for c in completions if c['result'] == 'SUCCESS')
            near_miss = sum(1 for c in completions if c['result'] == 'NEAR_MISS')
            lines.append(f"\n  Summary: {success} success, {near_miss} near-miss, {len(completions) - success - near_miss} incomplete")

        return "\n".join(lines)

    def render_metrics(self, metrics: Dict) -> str:
        """Render metrics summary."""
        lines = ["\n" + "=" * 70, "METRICS (24h)", "=" * 70]

        for name, values in metrics.items():
            total = values.get('total', 0)
            avg = values.get('avg')

            display = f"{total:.0f}" if isinstance(total, (int, float)) else str(total)
            if avg is not None:
                display += f" (avg: {avg:.1f})"

            lines.append(f"  {name:25s}: {display}")

        return "\n".join(lines)

    def render_dashboard(self) -> str:
        """Render full dashboard."""
        slots = self.get_slot_status()
        queue = self.get_queue_stats()
        completions = self.get_recent_completions()
        metrics = self.get_metrics_summary()

        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        header = f"\n{'#' * 70}\n# AGENTIC THEOREM PROVING DASHBOARD - {timestamp}\n{'#' * 70}\n"

        return (
            header +
            self.render_slots(slots) +
            self.render_queue(queue) +
            self.render_completions(completions) +
            self.render_metrics(metrics)
        )

    def display_once(self):
        """Display dashboard once."""
        print(self.render_dashboard())

    async def watch(self, interval: int = 30):
        """Continuously display dashboard."""
        while True:
            self.clear_screen()
            print(self.render_dashboard())
            print(f"\nRefreshing in {interval}s... (Ctrl+C to exit)")
            await asyncio.sleep(interval)


async def get_aristotle_status_live() -> Dict:
    """Get live Aristotle status."""
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
            })

        return by_status
    except Exception as e:
        return {'ERROR': [{'desc': str(e)}]}


def main():
    parser = argparse.ArgumentParser(description="Monitor Dashboard")
    parser.add_argument("--watch", action="store_true", help="Continuous watch mode")
    parser.add_argument("--interval", type=int, default=30, help="Refresh interval (seconds)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")

    args = parser.parse_args()

    dashboard = Dashboard()

    if args.json:
        data = {
            'slots': dashboard.get_slot_status(),
            'queue': dashboard.get_queue_stats(),
            'completions': dashboard.get_recent_completions(),
            'metrics': dashboard.get_metrics_summary()
        }
        print(json.dumps(data, indent=2, default=str))
    elif args.watch:
        try:
            asyncio.run(dashboard.watch(args.interval))
        except KeyboardInterrupt:
            print("\nDashboard stopped.")
    else:
        dashboard.display_once()


if __name__ == "__main__":
    main()
