#!/usr/bin/env python3
"""
Launch first Aristotle batch for Jones Unknotting Conjecture.
10 knots at 9 crossings with full context.
"""

import asyncio
from pathlib import Path
from aristotlelib import Project, ProjectInputType, set_api_key

async def launch_batch():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    input_file = Path("/Users/patrickkavanagh/math/unknotting/aristotle_batch_9crossing_test.txt")

    print("🚀 Launching first Jones Unknotting batch...")
    print(f"   Input file: {input_file.name}")
    print(f"   File size: {input_file.stat().st_size:,} bytes")
    print(f"   Task: Prove Jones ≠ 1 for 10 knots at 9 crossings")
    print(f"   Context: Full 626-line Jones polynomial framework included")
    print()

    try:
        # Launch asynchronously
        result = await Project.prove_from_file(
            input_file_path=str(input_file),
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False  # Don't wait, launch and continue
        )

        # When wait_for_completion=False, returns project_id as string
        project_id = result if isinstance(result, str) else result.id

        print("✅ Batch launched successfully!")
        print(f"   Project ID: {project_id}")
        print()
        print("📝 Saving project ID...")

        # Save project ID
        with open("/Users/patrickkavanagh/math/UNKNOTTING_9CROSSING_BATCH1_PROJECT_ID.txt", "w") as f:
            f.write(f"{project_id}\n")

        print("✅ Project ID saved to UNKNOTTING_9CROSSING_BATCH1_PROJECT_ID.txt")
        print()
        print("📊 Next steps:")
        print("   1. Monitor progress with check_queue.py")
        print("   2. Check status: aristotle (option 4 in TUI)")
        print("   3. Update GitHub with progress")

    except Exception as e:
        print(f"❌ Error launching batch: {e}")
        raise

asyncio.run(launch_batch())
