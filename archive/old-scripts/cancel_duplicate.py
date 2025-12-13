#!/usr/bin/env python3
"""Cancel duplicate Aristotle submission."""

import asyncio
from aristotlelib import Project, set_api_key

async def cancel_project():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    # The QUEUED duplicate
    duplicate_id = "841ddada-a994-4fbf-97f9-547c0a87fe60"

    print(f"🗑️  Canceling duplicate submission: {duplicate_id}")
    print()

    try:
        project = await Project.from_id(duplicate_id)
        await project.refresh()

        print(f"   Current status: {project.status}")

        if str(project.status) == "ProjectStatus.QUEUED":
            # Cancel it
            await project.cancel()
            print("   ✅ Cancelled successfully!")
            print()
            print("   Keeping the IN_PROGRESS one: 771e9804-7c02-4c86-b767-ac1b9f9742e1")
            print()

            # Update the saved project ID file
            with open("/Users/patrickkavanagh/math/UNKNOTTING_9CROSSING_BATCH1_PROJECT_ID.txt", "w") as f:
                f.write("771e9804-7c02-4c86-b767-ac1b9f9742e1\n")

            print("   ✅ Updated saved project ID to the active one")
        else:
            print(f"   ⚠️  Status is {project.status}, cannot cancel")

    except Exception as e:
        print(f"   ❌ Error: {e}")

asyncio.run(cancel_project())
