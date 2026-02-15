#!/usr/bin/env python3
"""One-shot migration: proven -> compiled_clean + add target_resolved."""
import sqlite3
import sys
from pathlib import Path

DB_PATH = Path(__file__).resolve().parent.parent / "submissions" / "tracking.db"

def migrate():
    conn = sqlite3.connect(str(DB_PATH))

    # Step 1: Add target_resolved column (idempotent)
    try:
        conn.execute("ALTER TABLE submissions ADD COLUMN target_resolved INTEGER DEFAULT 0")
        print("Added target_resolved column")
    except sqlite3.OperationalError as e:
        if "duplicate column" in str(e).lower():
            print("target_resolved column already exists")
        else:
            raise

    # Step 2: Rename status
    changed = conn.execute(
        "UPDATE submissions SET status = 'compiled_clean' WHERE status IN ('proven', 'PROVEN')"
    ).rowcount
    print(f"Migrated {changed} rows: proven -> compiled_clean")

    conn.commit()
    conn.close()

if __name__ == "__main__":
    migrate()
