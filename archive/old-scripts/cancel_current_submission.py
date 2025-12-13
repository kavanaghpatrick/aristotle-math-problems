#!/usr/bin/env python3
"""Cancel the current 25-crossing submission to resubmit optimized version."""

import asyncio
from aristotlelib import Project, set_api_key

async def cancel_submission():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    project_id = "4aef4bc7-ecf0-4e11-aab4-48da39ed3379"

    print("🛑 Canceling current submission for optimization...")
    print(f"Project ID: {project_id}")
    print()

    try:
        project = await Project.from_id(project_id)
        await project.refresh()

        print(f"Current status: {project.status}")

        if project.status in ['QUEUED', 'IN_PROGRESS']:
            print("⚠️  Note: Aristotle API may not support cancellation")
            print("   If project is running, it will complete")
            print("   We'll proceed with optimization anyway")
        else:
            print(f"✅ Project already in terminal state: {project.status}")

        print()
        print("📝 Reason for cancellation: Optimizing submission framing")
        print("   - Will provide PD codes instead of braid words")
        print("   - Will submit one knot at a time")
        print("   - Will provide Lean scaffolding")
        print("   - Will reduce context to 1-2 paragraphs")
        print()
        print("✅ Proceeding with optimization...")

    except Exception as e:
        print(f"ℹ️  Could not check/cancel: {e}")
        print("   Proceeding with optimization anyway...")

asyncio.run(cancel_submission())
