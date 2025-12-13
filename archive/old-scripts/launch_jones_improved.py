#!/usr/bin/env python3
"""
Launch improved Jones polynomial problem to Aristotle.
"""

import asyncio
import sys
from aristotlelib import Project, ProjectInputType, set_api_key

async def main():
    # Set API key
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🚀 Launching improved Jones polynomial problem to Aristotle...")
    print("📝 Input file: jones_improved_input.txt")
    print("🎯 Goals: O(c^3) upper bound, Ω(c) lower bound, concrete verification")
    print()

    try:
        # Launch the project
        project_id = await Project.prove_from_file(
            input_file_path="jones_improved_input.txt",
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False  # Don't wait, return immediately
        )

        print(f"✅ Successfully launched!")
        print(f"📦 Project ID: {project_id}")
        print()
        print("🔗 Monitor progress: https://aristotle.harmonic.fun/projects")
        print()

        # Write project ID to file
        with open("JONES_V2_PROJECT_ID.txt", "w") as f:
            f.write(f"{project_id}\n")

        print("💾 Project ID saved to: JONES_V2_PROJECT_ID.txt")

        return 0

    except Exception as e:
        print(f"❌ Error launching project: {e}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
