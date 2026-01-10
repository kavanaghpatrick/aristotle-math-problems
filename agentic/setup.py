#!/usr/bin/env python3
"""
Agentic System Setup - Initialize database and bootstrap queue
"""

import sqlite3
import argparse
from pathlib import Path
from datetime import datetime

from config import DB_PATH, AGENTIC_DIR, NU4_CASES, PROOF_STRATEGIES

def init_database():
    """Create additional tables for agentic system."""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()

    # Submission queue for validated items
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS submission_queue (
        id INTEGER PRIMARY KEY,
        file_path TEXT NOT NULL,
        priority INTEGER DEFAULT 50,
        case_name TEXT,
        approach TEXT,
        validation_stage TEXT DEFAULT 'pending',
        validation_passed INTEGER DEFAULT 0,
        validator_notes TEXT,
        failure_count INTEGER DEFAULT 0,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        submitted_at TEXT,
        aristotle_uuid TEXT,
        UNIQUE(file_path)
    )
    """)

    # Generator task tracking
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS generator_tasks (
        id INTEGER PRIMARY KEY,
        generator_type TEXT NOT NULL,
        target_case TEXT,
        strategy TEXT,
        base_file TEXT,
        status TEXT DEFAULT 'pending',
        output_file TEXT,
        error_message TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        started_at TEXT,
        completed_at TEXT
    )
    """)

    # Validation results
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS validation_results (
        id INTEGER PRIMARY KEY,
        file_path TEXT NOT NULL,
        stage TEXT NOT NULL,
        passed INTEGER NOT NULL,
        notes TEXT,
        validated_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (file_path) REFERENCES submission_queue(file_path)
    )
    """)

    # Metrics for dashboard
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS agentic_metrics (
        id INTEGER PRIMARY KEY,
        timestamp TEXT DEFAULT CURRENT_TIMESTAMP,
        metric_name TEXT NOT NULL,
        metric_value REAL NOT NULL,
        tags TEXT
    )
    """)

    # Aristotle slot tracking
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS aristotle_slots (
        slot_id INTEGER PRIMARY KEY,
        project_uuid TEXT,
        file_path TEXT,
        case_name TEXT,
        status TEXT DEFAULT 'empty',
        assigned_at TEXT,
        last_checked TEXT
    )
    """)

    # Initialize 15 slots
    for i in range(1, 16):
        cursor.execute("""
        INSERT OR IGNORE INTO aristotle_slots (slot_id, status)
        VALUES (?, 'empty')
        """, (i,))

    # Views for common queries
    cursor.execute("""
    CREATE VIEW IF NOT EXISTS v_queue_status AS
    SELECT
        case_name,
        COUNT(*) as count,
        AVG(priority) as avg_priority,
        SUM(CASE WHEN validation_passed = 1 THEN 1 ELSE 0 END) as validated
    FROM submission_queue
    WHERE submitted_at IS NULL
    GROUP BY case_name
    ORDER BY avg_priority DESC
    """)

    cursor.execute("""
    CREATE VIEW IF NOT EXISTS v_active_slots AS
    SELECT
        slot_id,
        project_uuid,
        file_path,
        case_name,
        status,
        assigned_at
    FROM aristotle_slots
    WHERE status != 'empty'
    ORDER BY slot_id
    """)

    conn.commit()
    conn.close()
    print(f"Database initialized at {DB_PATH}")

def create_directories():
    """Create necessary directories."""
    dirs = [
        AGENTIC_DIR / "logs",
        AGENTIC_DIR / "generators",
        AGENTIC_DIR / "validators",
        AGENTIC_DIR / "learning",
        AGENTIC_DIR / "monitor",
    ]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)
        # Create __init__.py
        init_file = d / "__init__.py"
        if not init_file.exists():
            init_file.write_text('"""Agentic system module."""\n')
    print("Directories created")

def seed_generator_tasks():
    """Seed initial generator tasks for all cases and strategies."""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()

    # Create tasks for each case x strategy combination
    for case in NU4_CASES[:4]:  # Focus on non-trivial cases
        for strategy in PROOF_STRATEGIES[:5]:  # Top 5 strategies
            cursor.execute("""
            INSERT OR IGNORE INTO generator_tasks
            (generator_type, target_case, strategy, status)
            VALUES ('proof', ?, ?, 'pending')
            """, (case, strategy))

    conn.commit()

    # Report
    cursor.execute("SELECT COUNT(*) FROM generator_tasks WHERE status='pending'")
    count = cursor.fetchone()[0]
    conn.close()
    print(f"Seeded {count} generator tasks")

def populate_initial_queue():
    """Find existing validated files and add to queue."""
    from pathlib import Path
    import glob

    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()

    # Find recent lean files
    lean_files = list(Path("submissions/nu4_final").glob("*.lean"))

    added = 0
    for f in lean_files:
        # Determine case from filename
        case_name = None
        for case in NU4_CASES:
            if case.replace('_', '') in f.stem.lower():
                case_name = case
                break

        cursor.execute("""
        INSERT OR IGNORE INTO submission_queue
        (file_path, case_name, validation_stage, priority)
        VALUES (?, ?, 'pending', 50)
        """, (str(f), case_name))

        if cursor.rowcount > 0:
            added += 1

    conn.commit()
    conn.close()
    print(f"Added {added} files to queue")

def main():
    parser = argparse.ArgumentParser(description="Agentic System Setup")
    parser.add_argument("--init-db", action="store_true", help="Initialize database tables")
    parser.add_argument("--create-dirs", action="store_true", help="Create directories")
    parser.add_argument("--seed-tasks", action="store_true", help="Seed generator tasks")
    parser.add_argument("--populate-queue", action="store_true", help="Add existing files to queue")
    parser.add_argument("--all", action="store_true", help="Do all setup steps")

    args = parser.parse_args()

    if args.all or args.init_db:
        init_database()
    if args.all or args.create_dirs:
        create_directories()
    if args.all or args.seed_tasks:
        seed_generator_tasks()
    if args.all or args.populate_queue:
        populate_initial_queue()

    if not any([args.init_db, args.create_dirs, args.seed_tasks, args.populate_queue, args.all]):
        parser.print_help()

if __name__ == "__main__":
    main()
