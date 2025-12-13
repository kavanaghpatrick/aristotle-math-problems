#!/usr/bin/env python3
"""Download Task 5 results."""

import asyncio
from aristotlelib import Project, set_api_key

async def download_task5():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    task5_id = "558d85ef-cf48-4aea-9b73-eedb44b75ede"

    print("📥 DOWNLOADING TASK 5 RESULTS")
    print("=" * 70)
    print(f"Project ID: {task5_id}")
    print()

    # Get project
    project = await Project.from_id(task5_id)
    await project.refresh()

    print(f"Status: {project.status.name}")
    print()

    # Get solution
    print("Retrieving solution...")
    solution_path = await project.get_solution()

    print(f"✅ Solution downloaded to: {solution_path}")
    print()

    # Copy to our directory
    import shutil
    dest = f"/Users/patrickkavanagh/math/aristotle_proofs/task5_4knots_{task5_id[:8]}_output.lean"
    shutil.copy(solution_path, dest)

    print(f"✅ Copied to: {dest}")
    print()

    # Read and display first 100 lines
    with open(dest, 'r') as f:
        lines = f.readlines()

    print("=" * 70)
    print(f"FILE PREVIEW (first 100 lines of {len(lines)} total)")
    print("=" * 70)
    for i, line in enumerate(lines[:100], 1):
        print(f"{i:4}: {line}", end='')

    print()
    print("=" * 70)
    print(f"📊 STATS")
    print("=" * 70)
    print(f"Total lines: {len(lines)}")
    print(f"File saved:  {dest}")
    print()

    return dest

if __name__ == "__main__":
    output_file = asyncio.run(download_task5())
    print(f"\n✅ Task 5 results downloaded: {output_file}")
