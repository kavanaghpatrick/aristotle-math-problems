#!/usr/bin/env python3
"""
Batch submit all 6 Parker strategy files to Aristotle.
Run when queue has ≥ 6 available slots.
"""

import asyncio
import aristotlelib
import os
import sqlite3
from datetime import datetime, timezone

aristotlelib.set_api_key(os.environ['ARISTOTLE_API_KEY'])

FILES = [
    {
        "path": "submissions/nu4_final/slot544_endpoint_no_base_external.lean",
        "slot": 544,
        "desc": "Parker: endpoint tau_le_2 when no base-edge external (0 sorry)",
        "sorry": 0,
        "proven": 13,
    },
    {
        "path": "submissions/nu4_final/slot545_parker_lemma_23.lean",
        "slot": 545,
        "desc": "Parker Lemma 2.3: tau(T_e)<=2 implies tau<=8 (0 sorry, 1 axiom)",
        "sorry": 0,
        "proven": 8,
    },
    {
        "path": "submissions/nu4_final/slot546_parker_disconnected.lean",
        "slot": 546,
        "desc": "Parker Lemma 2.4: disconnected matching tau<=8 (1 sorry)",
        "sorry": 1,
        "proven": 6,
    },
    {
        "path": "submissions/nu4_final/slot547_endpoint_replacement.lean",
        "slot": 547,
        "desc": "Endpoint replacement dichotomy: replace or bridge (0 sorry)",
        "sorry": 0,
        "proven": 10,
    },
    {
        "path": "submissions/nu4_final/slot548_path4_parker_complete.lean",
        "slot": 548,
        "desc": "PATH_4 tau<=8 when endpoint has no base-edge external (0 sorry, 1 axiom)",
        "sorry": 0,
        "proven": 12,
    },
    {
        "path": "submissions/nu4_final/slot549_tuza_nu4_assembly.lean",
        "slot": 549,
        "desc": "Tuza nu=4 universal assembly (1 genuine sorry, 2 axioms)",
        "sorry": 5,  # 1 genuine + 4 proof-in-other-file
        "proven": 0,
    },
]

DB_PATH = "submissions/tracking.db"


async def check_queue():
    """Check if queue has capacity."""
    projects, _ = await aristotlelib.Project.list_projects(limit=20)
    active = [p for p in projects
              if p.status.value in ('QUEUED', 'IN_PROGRESS', 'NOT_STARTED', 'PENDING_RETRY')]
    return len(active), 5 - len(active)


async def submit_file(info):
    """Submit a single file to Aristotle."""
    path = info["path"]
    slot = info["slot"]
    desc = info["desc"]

    print(f"\n{'='*60}")
    print(f"Submitting slot{slot}: {os.path.basename(path)}")
    print(f"  Description: {desc}")
    print(f"  Sorry: {info['sorry']}, Proven: {info['proven']}")

    try:
        result = await aristotlelib.Project.prove_from_file(
            input_file_path=path,
            project_input_type=aristotlelib.ProjectInputType.FORMAL_LEAN,
            wait_for_completion=False,
        )
        project_id = str(result)
        print(f"  PROJECT_ID: {project_id}")

        # Save ID file
        id_file = f"submissions/nu4_final/slot{slot}_parker_ID.txt"
        with open(id_file, "w") as f:
            f.write(f"{project_id}\n")
            f.write(f"# Submitted: {datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}\n")
            f.write(f"# {desc}\n")
        print(f"  ID saved to: {id_file}")

        # Update DB
        db = sqlite3.connect(DB_PATH)
        db.execute("""
            INSERT OR REPLACE INTO submissions
              (filename, uuid, problem_id, pattern, status,
               sorry_count, proven_count, frontier_id, notes, submitted_at)
            VALUES (?, ?, ?, 'scaffolded', 'submitted',
                    ?, ?, 'nu_4', ?, datetime('now'))
        """, (
            os.path.basename(path),
            project_id,
            f"slot{slot}",
            info["sorry"],
            info["proven"],
            desc,
        ))
        db.commit()
        db.close()
        print(f"  DB updated: YES")

        return project_id
    except Exception as e:
        print(f"  ERROR: {e}")
        return None


async def main():
    active, available = await check_queue()
    print(f"Queue: {active} active, {available} available")

    if available < 1:
        print("\nQUEUE FULL — cannot submit. Wait for jobs to complete.")
        return

    submitted = 0
    for info in FILES:
        if submitted >= available:
            print(f"\nQueue full after {submitted} submissions. Remaining files queued locally.")
            break

        pid = await submit_file(info)
        if pid:
            submitted += 1
            # Small delay between submissions
            await asyncio.sleep(2)

    print(f"\n{'='*60}")
    print(f"DONE: {submitted}/{len(FILES)} files submitted")
    print(f"Monitor with: python3 scripts/aristotle_monitor.py")


if __name__ == "__main__":
    asyncio.run(main())
