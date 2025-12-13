#!/usr/bin/env python3
"""Check status of Aristotle projects in queue."""

import asyncio
from aristotlelib import Project, ProjectStatus, set_api_key

async def check_queue():
    # Set API key
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🔍 CHECKING ARISTOTLE QUEUE STATUS")
    print("=" * 70)

    # Read our project IDs
    with open("/Users/patrickkavanagh/math/task5_6_project_ids.txt", "r") as f:
        lines = f.readlines()

    task5_id = lines[0].split(": ")[1].strip()
    task6_id = lines[1].split(": ")[1].strip()

    print(f"\nOur Submitted Projects:")
    print(f"  Task 5 (4 Knots):        {task5_id}")
    print(f"  Task 6 (Reidemeister):   {task6_id}")
    print()

    # Check Task 5 status
    print("=" * 70)
    print("TASK 5: Verify 4 Additional Knots (6₁, 6₂, 6₃, 7₁)")
    print("=" * 70)
    try:
        task5_project = await Project.from_id(task5_id)
        await task5_project.refresh()

        print(f"Status:      {task5_project.status.name}")
        print(f"Created:     {task5_project.created_at if hasattr(task5_project, 'created_at') else 'N/A'}")

        # Status descriptions
        status_info = {
            ProjectStatus.QUEUED: "⏳ Waiting in queue for processing",
            ProjectStatus.IN_PROGRESS: "🔄 Currently being processed by Aristotle",
            ProjectStatus.COMPLETE: "✅ Successfully completed!",
            ProjectStatus.FAILED: "❌ Failed during processing",
            ProjectStatus.PENDING_RETRY: "🔄 Retrying after an error"
        }

        if task5_project.status in status_info:
            print(f"Description: {status_info[task5_project.status]}")

    except Exception as e:
        print(f"❌ Error checking Task 5: {e}")

    print()

    # Check Task 6 status
    print("=" * 70)
    print("TASK 6: Reidemeister Invariance Proof")
    print("=" * 70)
    try:
        task6_project = await Project.from_id(task6_id)
        await task6_project.refresh()

        print(f"Status:      {task6_project.status.name}")
        print(f"Created:     {task6_project.created_at if hasattr(task6_project, 'created_at') else 'N/A'}")

        if task6_project.status in status_info:
            print(f"Description: {status_info[task6_project.status]}")

    except Exception as e:
        print(f"❌ Error checking Task 6: {e}")

    print()

    # List all recent projects
    print("=" * 70)
    print("ALL RECENT PROJECTS (Last 10)")
    print("=" * 70)
    try:
        projects, _ = await Project.list_projects(limit=10)

        print(f"\n{'Project ID':<40} {'Status':<20} {'Name/Type'}")
        print("-" * 100)

        for p in projects:
            # Truncate project ID for display
            project_id_short = p.project_id[:36] if len(p.project_id) > 36 else p.project_id

            # Get project name if available
            project_name = "N/A"
            if hasattr(p, 'name') and p.name:
                project_name = p.name[:30]

            # Mark our projects
            marker = ""
            if p.project_id == task5_id:
                marker = " ← Task 5"
                project_name = "4 Knots Verification"
            elif p.project_id == task6_id:
                marker = " ← Task 6"
                project_name = "Reidemeister Invariance"

            print(f"{project_id_short:<40} {p.status.name:<20} {project_name}{marker}")

    except Exception as e:
        print(f"❌ Error listing projects: {e}")

    print()
    print("=" * 70)
    print("QUEUE SUMMARY")
    print("=" * 70)

    # Count statuses
    try:
        statuses = {}
        for p in projects:
            status_name = p.status.name
            statuses[status_name] = statuses.get(status_name, 0) + 1

        for status_name, count in sorted(statuses.items()):
            emoji = {
                "QUEUED": "⏳",
                "IN_PROGRESS": "🔄",
                "COMPLETE": "✅",
                "FAILED": "❌",
                "PENDING_RETRY": "🔄"
            }.get(status_name, "❓")

            print(f"{emoji} {status_name:<20} {count} project(s)")

    except Exception as e:
        print(f"Error calculating summary: {e}")

    print()
    print("=" * 70)
    print("💡 To monitor continuously: run this script in a loop")
    print("💡 Or use: aristotle (TUI) and select option 4 for history")
    print("=" * 70)

if __name__ == "__main__":
    asyncio.run(check_queue())
