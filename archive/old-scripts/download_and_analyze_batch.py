#!/usr/bin/env python3
"""Download and analyze first batch results."""

import asyncio
from pathlib import Path
from aristotlelib import Project, set_api_key

async def download_and_analyze():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    project_id = "771e9804-7c02-4c86-b767-ac1b9f9742e1"

    print("📥 DOWNLOADING FIRST BATCH RESULTS")
    print("=" * 70)
    print(f"Project ID: {project_id}")
    print()

    try:
        # Get project
        project = await Project.from_id(project_id)
        await project.refresh()

        print(f"Status: {project.status}")
        print(f"Created: {project.created_at}")
        print()

        # Download solution
        print("⬇️  Downloading solution...")
        solution_path = await project.get_solution()

        print(f"✅ Downloaded to: {solution_path}")
        print()

        # Copy to our workspace
        output_file = Path(f"/Users/patrickkavanagh/math/unknotting_batch1_{project_id[:8]}_output.lean")

        with open(solution_path, 'r') as src:
            content = src.read()

        with open(output_file, 'w') as dst:
            dst.write(content)

        print(f"✅ Copied to: {output_file.name}")
        print()

        # Quick analysis
        lines = content.split('\n')
        print("📊 QUICK ANALYSIS")
        print("-" * 70)
        print(f"Total lines: {len(lines)}")

        # Count theorems
        theorem_count = sum(1 for line in lines if 'theorem' in line.lower())
        sorry_count = sum(1 for line in lines if 'sorry' in line.lower())

        print(f"Theorems found: {theorem_count}")
        print(f"Sorries found: {sorry_count}")
        print()

        if sorry_count == 0:
            print("✅ NO SORRIES - All proofs complete!")
        else:
            print(f"⚠️  {sorry_count} sorries found - partial completion")

        print()
        print("📝 Next steps:")
        print(f"   1. Review: cat {output_file.name}")
        print("   2. Validate Jones polynomials match KnotInfo")
        print("   3. Update GitHub with results")
        print("   4. Prepare next batch (10 crossings)")

    except Exception as e:
        print(f"❌ Error: {e}")
        import traceback
        traceback.print_exc()

asyncio.run(download_and_analyze())
