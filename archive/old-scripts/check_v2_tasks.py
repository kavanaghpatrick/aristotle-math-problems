#!/usr/bin/env python3
"""Check status of Task 5 v2 and Task 6 v2."""

import asyncio
from aristotlelib import Project, ProjectStatus, set_api_key
from datetime import datetime

async def check_v2_tasks():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🔍 CHECKING TASKS 5 V2 & 6 V2 STATUS")
    print("=" * 70)

    # Read project IDs
    with open("/Users/patrickkavanagh/math/tasks_v2_project_ids.txt", "r") as f:
        lines = f.readlines()

    task5_v2_id = lines[0].split(": ")[1].strip()
    task6_v2_id = lines[1].split(": ")[1].strip()

    print(f"\nSubmitted Tasks:")
    print(f"  Task 5 v2 (4 Knots):        {task5_v2_id}")
    print(f"  Task 6 v2 (Reidemeister):   {task6_v2_id}")
    print()

    # Status descriptions
    status_info = {
        ProjectStatus.QUEUED: "⏳ Waiting in queue",
        ProjectStatus.IN_PROGRESS: "🔄 Currently processing",
        ProjectStatus.COMPLETE: "✅ Successfully completed!",
        ProjectStatus.FAILED: "❌ Failed",
        ProjectStatus.PENDING_RETRY: "🔄 Retrying",
        ProjectStatus.NOT_STARTED: "⏸️ Not started"
    }

    # Check Task 5 v2
    print("=" * 70)
    print("TASK 5 V2: Verify 4 Additional Knots (6₁, 6₂, 6₃, 7₁)")
    print("=" * 70)
    try:
        task5 = await Project.from_id(task5_v2_id)
        await task5.refresh()

        print(f"Status:      {task5.status.name}")
        print(f"Created:     {task5.created_at if hasattr(task5, 'created_at') else 'N/A'}")

        if task5.status in status_info:
            print(f"Description: {status_info[task5.status]}")

        # Calculate elapsed time
        if hasattr(task5, 'created_at') and task5.created_at:
            created = task5.created_at
            now = datetime.now(created.tzinfo)
            elapsed = now - created
            elapsed_mins = int(elapsed.total_seconds() / 60)
            print(f"Elapsed:     {elapsed_mins} minutes")

            if task5.status == ProjectStatus.IN_PROGRESS:
                print(f"Expected:    ~180 minutes (3 hours)")
                remaining = 180 - elapsed_mins
                if remaining > 0:
                    print(f"Remaining:   ~{remaining} minutes")

    except Exception as e:
        print(f"❌ Error: {e}")

    print()

    # Check Task 6 v2
    print("=" * 70)
    print("TASK 6 V2: Reidemeister Invariance Proof")
    print("=" * 70)
    try:
        task6 = await Project.from_id(task6_v2_id)
        await task6.refresh()

        print(f"Status:      {task6.status.name}")
        print(f"Created:     {task6.created_at if hasattr(task6, 'created_at') else 'N/A'}")

        if task6.status in status_info:
            print(f"Description: {status_info[task6.status]}")

        # Calculate elapsed time
        if hasattr(task6, 'created_at') and task6.created_at:
            created = task6.created_at
            now = datetime.now(created.tzinfo)
            elapsed = now - created
            elapsed_mins = int(elapsed.total_seconds() / 60)
            print(f"Elapsed:     {elapsed_mins} minutes")

            if task6.status == ProjectStatus.IN_PROGRESS:
                print(f"Expected:    ~780 minutes (13 hours)")
                remaining = 780 - elapsed_mins
                if remaining > 0:
                    print(f"Remaining:   ~{remaining} minutes (~{remaining/60:.1f} hours)")

    except Exception as e:
        print(f"❌ Error: {e}")

    print()

    # Overall summary
    print("=" * 70)
    print("📊 SUMMARY")
    print("=" * 70)

    try:
        task5_status = task5.status.name
        task6_status = task6.status.name

        print(f"Task 5 v2 (4 Knots):        {task5_status}")
        print(f"Task 6 v2 (Reidemeister):   {task6_status}")
        print()

        if task5.status == ProjectStatus.COMPLETE:
            print("🎉 Task 5 v2 is COMPLETE! Download results to analyze.")
        elif task5.status == ProjectStatus.IN_PROGRESS:
            print("⏳ Task 5 v2 is still running...")

        if task6.status == ProjectStatus.COMPLETE:
            print("🎉 Task 6 v2 is COMPLETE! Download results to analyze.")
        elif task6.status == ProjectStatus.IN_PROGRESS:
            print("⏳ Task 6 v2 is still running...")

        if task5.status == ProjectStatus.FAILED or task6.status == ProjectStatus.FAILED:
            print("⚠️ One or more tasks failed - check error messages")

    except Exception as e:
        print(f"Error in summary: {e}")

    print("=" * 70)

if __name__ == "__main__":
    asyncio.run(check_v2_tasks())
