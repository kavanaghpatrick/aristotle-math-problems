#!/usr/bin/env python3
"""Launch Task 5 (4 knots) and Task 6 (Reidemeister invariance) to Aristotle."""

import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key

async def launch_tasks():
    # Set API key
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🚀 Launching Task 5: Verify 4 Additional Knots (6₁, 6₂, 6₃, 7₁)")
    print("=" * 70)

    # Launch Task 5 - returns project ID string when wait_for_completion=False
    task5_id = await Project.prove_from_file(
        input_file_path="/Users/patrickkavanagh/math/task5_verify_4_knots.txt",
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=False  # Don't wait, return immediately with project ID
    )

    print(f"✅ Task 5 submitted successfully!")
    print(f"   Project ID: {task5_id}")
    print()

    print("🚀 Launching Task 6: Reidemeister Invariance Proof")
    print("=" * 70)

    # Launch Task 6 - returns project ID string when wait_for_completion=False
    task6_id = await Project.prove_from_file(
        input_file_path="/Users/patrickkavanagh/math/task6_reidemeister_invariance.txt",
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=False  # Don't wait, return immediately with project ID
    )

    print(f"✅ Task 6 submitted successfully!")
    print(f"   Project ID: {task6_id}")
    print()

    print("=" * 70)
    print("📊 SUMMARY")
    print("=" * 70)
    print(f"Task 5 (4 Knots):         {task5_id}")
    print(f"Task 6 (Reidemeister):    {task6_id}")
    print()
    print("💡 Monitor progress with:")
    print("   aristotle  # then select option 4 for history")
    print()
    print("📝 Save these project IDs for later reference!")

    return task5_id, task6_id

if __name__ == "__main__":
    task5_id, task6_id = asyncio.run(launch_tasks())

    # Write project IDs to a file for later reference
    with open("/Users/patrickkavanagh/math/task5_6_project_ids.txt", "w") as f:
        f.write(f"Task 5 (4 Knots): {task5_id}\n")
        f.write(f"Task 6 (Reidemeister Invariance): {task6_id}\n")

    print(f"\n✅ Project IDs saved to: task5_6_project_ids.txt")
