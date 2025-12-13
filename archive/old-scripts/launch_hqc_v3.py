#!/usr/bin/env python3
"""
Launch HQC v3 to Aristotle - exploit quasi-cyclic structure!
"""

import asyncio
import sys
from aristotlelib import Project, ProjectInputType, set_api_key

async def main():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🚀 Launching HQC v3: Exploiting Quasi-Cyclic Structure")
    print()
    print("📝 Input file: hqc_v3_input.txt")
    print("🎯 Goals:")
    print("   1. Automorphism group C_83 analysis (ISD orbit structure)")
    print("   2. FFT eigenvalue analysis (circulant matrices)")
    print("   3. Polynomial ring representation (Gröbner basis)")
    print("   4. Independence assumption verification")
    print("   5. Dual code QC structure analysis")
    print()
    print("🔬 Novelty Target: 7-8/10 (vs v2's 5-6/10)")
    print("📏 Target Length: 250-400 lines (vs v2's 111-167)")
    print("✨ Key Innovation: FORCES QC structure exploitation")
    print()

    try:
        project_id = await Project.prove_from_file(
            input_file_path="hqc_v3_input.txt",
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False
        )

        print("✅ Successfully launched HQC v3!")
        print(f"📦 Project ID: {project_id}")
        print()
        print("🔗 Monitor: https://aristotle.harmonic.fun/projects")
        print()

        # Save project ID
        with open("HQC_V3_PROJECT_ID.txt", "w") as f:
            f.write(f"{project_id}\n")

        print("💾 Project ID saved to: HQC_V3_PROJECT_ID.txt")
        print()
        print("📊 Comparison:")
        print("   v1: 97 lines, 1 attack, 4/10 novelty")
        print("   v2: 111-167 lines, 2 attacks, 5-6/10 novelty (generic bounds)")
        print("   v3: Target 250-400 lines, QC exploitation, 7-8/10 novelty")
        print()
        print("⏱️  Expected: 3-16 hours")

        return 0

    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
