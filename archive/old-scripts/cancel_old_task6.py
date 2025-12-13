#!/usr/bin/env python3
"""Try to cancel the old Task 6 v1 that's missing context."""

import asyncio
from aristotlelib import Project, set_api_key

async def cancel_old_task6():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    old_task6_id = "bcfcb129-f7a3-4c1c-89e0-9b8e7ba4b4d6"

    print("🛑 ATTEMPTING TO CANCEL OLD TASK 6 V1")
    print("=" * 70)
    print(f"Project ID: {old_task6_id}")
    print()

    # Try to get the project
    try:
        project = await Project.from_id(old_task6_id)
        await project.refresh()

        print(f"Current status: {project.status.name}")
        print()

        # Check if there's a cancel or delete method
        print("Checking for cancel/delete methods...")
        methods = [attr for attr in dir(project) if not attr.startswith('_')]

        # Look for cancel/delete/stop methods
        cancel_methods = [m for m in methods if 'cancel' in m.lower() or 'delete' in m.lower() or 'stop' in m.lower()]

        if cancel_methods:
            print(f"Found potential cancel methods: {cancel_methods}")

            # Try each one
            for method in cancel_methods:
                try:
                    func = getattr(project, method)
                    if callable(func):
                        print(f"\nTrying {method}()...")
                        result = await func() if asyncio.iscoroutinefunction(func) else func()
                        print(f"✅ {method}() succeeded: {result}")
                        break
                except Exception as e:
                    print(f"❌ {method}() failed: {e}")
        else:
            print("❌ No cancel/delete methods found in the API")
            print()
            print("Available methods:")
            for m in methods[:20]:  # Show first 20
                print(f"  - {m}")
            print()
            print("⚠️ The Aristotle Python API may not support cancellation.")
            print("The old task will likely complete or fail on its own.")
            print("It will fail when it discovers the missing context.")

    except Exception as e:
        print(f"❌ Error: {e}")

    print()
    print("=" * 70)
    print("NOTE: Even if we can't cancel it, the old task will fail")
    print("when it realizes the Jones v2 context is missing.")
    print("The new Task 6 v2 has the context and should succeed.")
    print("=" * 70)

if __name__ == "__main__":
    asyncio.run(cancel_old_task6())
