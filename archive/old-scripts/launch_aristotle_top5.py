#!/usr/bin/env python3
"""
Launch Aristotle proofs for TOP 5 problems in parallel
"""
import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key
import time

# Set API key
set_api_key("os.environ["ARISTOTLE_API_KEY"]")

problems = [
    {
        "name": "Issue #21: Spectral Gap Bounds (30-45%)",
        "file": "/Users/patrickkavanagh/math/aristotle-problems/problem_21_spectral_gap.txt",
        "issue_num": 21
    },
    {
        "name": "Issue #23: Sorting Networks (35%)",
        "file": "/Users/patrickkavanagh/math/aristotle-problems/problem_23_sorting_networks.txt",
        "issue_num": 23
    },
    {
        "name": "Issue #25: Resolution Complexity (35%)",
        "file": "/Users/patrickkavanagh/math/aristotle-problems/problem_25_resolution_complexity.txt",
        "issue_num": 25
    },
    {
        "name": "Issue #22: QC Syndrome Decoding (30-40%)",
        "file": "/Users/patrickkavanagh/math/aristotle-problems/problem_22_qc_syndrome.txt",
        "issue_num": 22
    },
    {
        "name": "Issue #24: Jones Polynomial (30-40%)",
        "file": "/Users/patrickkavanagh/math/aristotle-problems/problem_24_jones_polynomial.txt",
        "issue_num": 24
    }
]

async def launch_proof(problem):
    """Launch a single proof without waiting"""
    print(f"\n🚀 Launching: {problem['name']}")
    print(f"   File: {problem['file']}")

    try:
        # Launch without waiting (async mode)
        project = await Project.prove_from_file(
            input_file_path=problem['file'],
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False  # Don't wait - launch in background
        )

        print(f"   ✅ Launched! Project ID: {project.id}")
        print(f"   Status: {project.status}")
        print(f"   Monitor at: https://aristotle.harmonic.fun/project/{project.id}")

        return {
            "problem": problem,
            "project_id": project.id,
            "status": project.status
        }

    except Exception as e:
        print(f"   ❌ Error: {e}")
        return {
            "problem": problem,
            "error": str(e)
        }

async def main():
    print("=" * 80)
    print("LAUNCHING ARISTOTLE ON TOP 5 PROBLEMS - PARALLEL EXECUTION")
    print("=" * 80)

    # Launch all proofs in parallel
    results = await asyncio.gather(*[launch_proof(p) for p in problems])

    print("\n" + "=" * 80)
    print("LAUNCH SUMMARY")
    print("=" * 80)

    successful = []
    failed = []

    for result in results:
        if "error" in result:
            failed.append(result)
            print(f"\n❌ FAILED: {result['problem']['name']}")
            print(f"   Error: {result['error']}")
        else:
            successful.append(result)
            print(f"\n✅ RUNNING: {result['problem']['name']}")
            print(f"   Project ID: {result['project_id']}")
            print(f"   Issue: https://github.com/kavanaghpatrick/aristotle-math-problems/issues/{result['problem']['issue_num']}")

    print("\n" + "=" * 80)
    print(f"RESULTS: {len(successful)}/5 launched successfully")
    print("=" * 80)

    # Save project IDs to file
    with open("/Users/patrickkavanagh/math/aristotle_project_ids.txt", "w") as f:
        f.write("ARISTOTLE PROJECT IDs - TOP 5 PROBLEMS\n")
        f.write("=" * 60 + "\n\n")
        for result in successful:
            f.write(f"{result['problem']['name']}\n")
            f.write(f"  Project ID: {result['project_id']}\n")
            f.write(f"  GitHub Issue: https://github.com/kavanaghpatrick/aristotle-math-problems/issues/{result['problem']['issue_num']}\n")
            f.write(f"  Aristotle: https://aristotle.harmonic.fun/project/{result['project_id']}\n\n")

    print("\n📝 Project IDs saved to: /Users/patrickkavanagh/math/aristotle_project_ids.txt")

    print("\n💡 To check status later:")
    print("   1. Visit Aristotle dashboard: https://aristotle.harmonic.fun")
    print("   2. Use Python API: await Project.get_project_by_id(project_id)")
    print("   3. CLI: aristotle history")

if __name__ == "__main__":
    asyncio.run(main())
