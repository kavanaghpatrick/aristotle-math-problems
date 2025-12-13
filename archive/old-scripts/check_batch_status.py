#!/usr/bin/env python3
"""Quick check on first batch status."""

import asyncio
from aristotlelib import Project, set_api_key

async def check():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    project_id = "771e9804-7c02-4c86-b767-ac1b9f9742e1"

    print(f"🔍 Checking First Batch Status")
    print(f"Project ID: {project_id}")
    print()

    try:
        project = await Project.from_id(project_id)
        await project.refresh()

        print(f"✅ Status: {project.status}")
        print(f"   Created: {project.created_at}")

        if str(project.status) == "ProjectStatus.COMPLETE":
            print()
            print("🎉 BATCH IS COMPLETE!")
            print("   Next: python3 download_and_analyze_batch.py")
        elif str(project.status) == "ProjectStatus.FAILED":
            print()
            print("❌ BATCH FAILED!")
            print("   Check logs for details")
        else:
            print()
            print("⏳ Still running... check back later")

    except Exception as e:
        print(f"❌ Error: {e}")
        print()
        print("Possible causes:")
        print("  - API server issue")
        print("  - Network connectivity")
        print("  - Project ID invalid")
        print()
        print("Try again in a few minutes or use Aristotle TUI")

asyncio.run(check())
