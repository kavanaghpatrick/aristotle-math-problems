#!/usr/bin/env python3
"""
Mass launch all 7 improved problems to Aristotle.
"""

import asyncio
import os
import sys
from aristotlelib import Project, ProjectInputType, set_api_key

# Problem files in priority order
PROBLEMS = [
    ("01_quantum_query_collision.txt", "Issue #27 - Quantum Query Collision (n=16)", "#27"),
    ("02_quantum_communication_disjointness.txt", "Issue #28 - Quantum Communication Disjointness (n=8)", "#28"),
    ("03_php_width_improved.txt", "Issue #25 - PHP Width (PHP_5 improved)", "#25"),
    ("04_self_dual_code.txt", "Issue #32 - Self-Dual Code [56,28,12]", "#32"),
    ("05_sorting_network_optimal.txt", "Issue #23 - Sorting Network C(18)=77 (improved)", "#23"),
    ("06_polynomial_calculus_space.txt", "Issue #35 - PC Space (PHP_6)", "#35"),
    ("07_qaoa_maxcut.txt", "Issue #41 - QAOA MaxCut 3-Regular", "#41"),
]

async def launch_all():
    set_api_key(os.environ.get("ARISTOTLE_API_KEY"))
    if not os.environ.get("ARISTOTLE_API_KEY"):
        raise ValueError("ARISTOTLE_API_KEY environment variable not set")

    print("🚀 MASS LAUNCH: 7 Improved Problems")
    print("=" * 60)
    print()

    project_ids = []

    for i, (filename, description, issue) in enumerate(PROBLEMS, 1):
        print(f"[{i}/7] Launching: {description}")
        print(f"       File: {filename}")
        print(f"       Issue: {issue}")

        try:
            project_id = await Project.prove_from_file(
                input_file_path=f"mass_launch/{filename}",
                project_input_type=ProjectInputType.INFORMAL,
                wait_for_completion=False
            )

            print(f"       ✅ SUCCESS - Project ID: {project_id}")
            project_ids.append((issue, description, project_id))

        except Exception as e:
            print(f"       ❌ ERROR: {e}")
            project_ids.append((issue, description, f"FAILED: {e}"))

        print()

    print("=" * 60)
    print("📊 LAUNCH SUMMARY")
    print("=" * 60)
    print()

    successful = sum(1 for _, _, pid in project_ids if not pid.startswith("FAILED"))
    print(f"✅ Successful: {successful}/7")
    print(f"❌ Failed: {7 - successful}/7")
    print()

    print("📦 Project IDs:")
    print()
    for issue, desc, pid in project_ids:
        status = "✅" if not pid.startswith("FAILED") else "❌"
        print(f"{status} {issue}: {pid}")
    print()

    # Save to file
    with open("mass_launch/PROJECT_IDS.txt", "w") as f:
        f.write("# Mass Launch Project IDs\n")
        f.write("# Date: 2025-12-11\n")
        f.write("# Total: 7 problems\n\n")
        for issue, desc, pid in project_ids:
            f.write(f"{issue}: {pid}\n")
            f.write(f"  # {desc}\n\n")

    print("💾 Project IDs saved to: mass_launch/PROJECT_IDS.txt")
    print()

    print("🔗 Monitor progress:")
    print("   https://aristotle.harmonic.fun/projects")
    print()

    print("📋 Next Steps:")
    print("   1. Monitor all 7 projects (3-16 hours each)")
    print("   2. When complete, verify QC/structure exploitation")
    print("   3. Update GitHub issues with results")
    print("   4. Compare to success criteria")
    print()

    return 0 if successful == 7 else 1

if __name__ == "__main__":
    sys.exit(asyncio.run(launch_all()))
