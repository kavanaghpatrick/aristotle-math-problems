#!/usr/bin/env python3
"""Check all recent Aristotle projects and identify which ones are ours."""

import asyncio
from aristotlelib import Project, ProjectStatus, set_api_key

async def check_all_projects():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("📊 ALL RECENT ARISTOTLE PROJECTS")
    print("=" * 100)
    print()

    # Known project IDs from our work
    known_projects = {
        "cd691d07-ed92-4e2e-902f-5d9d0c3d1103": "Quantum Query Collision #27",
        "2e358cc4-caf3-4e75-846d-60da35fb9b1e": "Jones v2",
        "4c28f37f-7c1a-4a71-9843-f0ebaee07b8a": "HQC v3",
        "558d85ef-cf48-4aea-9b73-eedb44b75ede": "Task 5 v1 (failed - no context)",
        "bcfcb129-f7a3-4c1c-89e0-9b8e7ba4b4d6": "Task 6 v1 (will fail - no context)",
        "ad54d62b-5420-423c-b1da-4ecb46438de7": "Task 5 v2 (4 Knots - with context)",
        "c8bab1f9-45e2-4318-b0bf-d34e717a617e": "Task 6 v2 (Reidemeister - with context)",
    }

    # Get all recent projects
    try:
        projects, _ = await Project.list_projects(limit=30)

        print(f"{'Project ID':<40} {'Status':<15} {'Created':<25} {'Description'}")
        print("-" * 100)

        completed = []
        in_progress = []
        failed = []
        other = []

        for p in projects:
            project_id_short = p.project_id[:36] if len(p.project_id) > 36 else p.project_id
            status_emoji = {
                ProjectStatus.COMPLETE: "✅",
                ProjectStatus.IN_PROGRESS: "🔄",
                ProjectStatus.FAILED: "❌",
                ProjectStatus.QUEUED: "⏳",
                ProjectStatus.PENDING_RETRY: "🔄",
                ProjectStatus.NOT_STARTED: "⏸️"
            }.get(p.status, "❓")

            # Get description
            description = known_projects.get(p.project_id, "Unknown")

            # Format created time
            created_str = str(p.created_at)[:19] if hasattr(p, 'created_at') else "N/A"

            print(f"{project_id_short:<40} {status_emoji} {p.status.name:<13} {created_str:<25} {description}")

            # Categorize
            if p.status == ProjectStatus.COMPLETE:
                completed.append((p.project_id, description))
            elif p.status == ProjectStatus.IN_PROGRESS:
                in_progress.append((p.project_id, description))
            elif p.status == ProjectStatus.FAILED:
                failed.append((p.project_id, description))
            else:
                other.append((p.project_id, p.status.name, description))

        print()
        print("=" * 100)
        print("📊 SUMMARY BY STATUS")
        print("=" * 100)
        print()

        print(f"✅ COMPLETED ({len(completed)}):")
        for pid, desc in completed:
            marker = " ← OURS" if pid in known_projects else ""
            print(f"   - {desc}{marker}")

        print()
        print(f"🔄 IN PROGRESS ({len(in_progress)}):")
        for pid, desc in in_progress:
            marker = " ← OURS" if pid in known_projects else ""
            print(f"   - {desc}{marker}")

        print()
        if failed:
            print(f"❌ FAILED ({len(failed)}):")
            for pid, desc in failed:
                marker = " ← OURS" if pid in known_projects else ""
                print(f"   - {desc}{marker}")
            print()

        if other:
            print(f"❓ OTHER ({len(other)}):")
            for pid, status, desc in other:
                marker = " ← OURS" if pid in known_projects else ""
                print(f"   - {desc} ({status}){marker}")
            print()

        print("=" * 100)
        print("🎯 OUR PROJECTS STATUS")
        print("=" * 100)
        print()

        our_projects = [p for p in projects if p.project_id in known_projects]

        for p in our_projects:
            desc = known_projects[p.project_id]
            status_emoji = {
                ProjectStatus.COMPLETE: "✅",
                ProjectStatus.IN_PROGRESS: "🔄",
                ProjectStatus.FAILED: "❌"
            }.get(p.status, "❓")

            print(f"{status_emoji} {desc:<50} {p.status.name}")

    except Exception as e:
        print(f"❌ Error: {e}")

if __name__ == "__main__":
    asyncio.run(check_all_projects())
