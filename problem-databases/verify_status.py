#!/usr/bin/env python3
"""
Verify problem status by checking erdosproblems.com
Updates database with correct status and verification date.
"""

import sqlite3
import re
import time
from pathlib import Path
from urllib.request import urlopen, Request
from datetime import datetime

DB_PATH = Path(__file__).parent / "problems.db"
LOG_FILE = Path(__file__).parent / "verification_log.txt"

def log(msg):
    print(msg, flush=True)
    with open(LOG_FILE, 'a') as f:
        f.write(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}\n")

def fetch_status(problem_id):
    """Fetch status from erdosproblems.com"""
    url = f"https://www.erdosproblems.com/{problem_id}"
    headers = {'User-Agent': 'Mozilla/5.0'}

    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=15) as response:
            html = response.read().decode('utf-8')

            # Check for status indicators
            if 'PROVED' in html or '>SOLVED<' in html.upper():
                return 'solved'
            elif 'DISPROVED' in html:
                return 'disproved'
            elif '>OPEN<' in html.upper() or 'This is open' in html:
                return 'open'
            elif 'PARTIALLY' in html.upper():
                return 'partial'
            else:
                return None
    except Exception as e:
        return None

def main(check_unknown=True, check_open=False, limit=100):
    """Verify problem statuses."""

    with open(LOG_FILE, 'w') as f:
        f.write(f"=== STATUS VERIFICATION {datetime.now()} ===\n\n")

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    # Build query based on what to check
    if check_unknown:
        query = "SELECT id, source_id FROM problems WHERE source='erdos' AND status='unknown' LIMIT ?"
    elif check_open:
        query = "SELECT id, source_id FROM problems WHERE source='erdos' AND status='open' AND verified_date IS NULL LIMIT ?"
    else:
        query = "SELECT id, source_id FROM problems WHERE source='erdos' AND verified_date IS NULL LIMIT ?"

    cursor = conn.execute(query, (limit,))
    problems = list(cursor)

    log(f"Checking {len(problems)} problems...")

    updated = 0
    changes = {'open': 0, 'solved': 0, 'disproved': 0, 'partial': 0, 'unchanged': 0, 'failed': 0}

    for i, row in enumerate(problems, 1):
        pid = row['source_id']
        new_status = fetch_status(pid)

        if new_status:
            # Get current status
            cur = conn.execute("SELECT status FROM problems WHERE id=?", (row['id'],)).fetchone()
            old_status = cur['status'] if cur else 'unknown'

            if old_status != new_status:
                conn.execute("""
                    UPDATE problems
                    SET status = ?, verified_date = ?
                    WHERE id = ?
                """, (new_status, datetime.now().strftime('%Y-%m-%d'), row['id']))
                log(f"  #{pid}: {old_status} → {new_status}")
                changes[new_status] = changes.get(new_status, 0) + 1
                updated += 1
            else:
                conn.execute("UPDATE problems SET verified_date = ? WHERE id = ?",
                           (datetime.now().strftime('%Y-%m-%d'), row['id']))
                changes['unchanged'] += 1
        else:
            changes['failed'] += 1

        if i % 20 == 0:
            log(f"Progress: {i}/{len(problems)}")
            conn.commit()

        time.sleep(0.3)

    conn.commit()
    conn.close()

    log(f"\n=== COMPLETE ===")
    log(f"Updated: {updated}")
    log(f"Changes: {changes}")

if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == '--open':
        main(check_unknown=False, check_open=True, limit=200)
    elif len(sys.argv) > 1 and sys.argv[1] == '--all':
        main(check_unknown=False, check_open=False, limit=500)
    else:
        main(check_unknown=True, limit=100)
