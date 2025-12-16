#!/usr/bin/env python3
"""
Submit all 5 Boris-style problems to Aristotle.

Submission order (by recommended priority):
1. Erdős Discrepancy C=3 (Pure SAT, 25%)
2. R(5,5) Exact Value (SAT-heavy, 5%)
3. Extremal Code [72,36,16] (Algebraic, 10%)
4. Union-Closed N=13 (Lattice, 15%)
5. MOLS(10) (Moonshot, <1%)
"""

import asyncio
import os
import sys
from pathlib import Path
from datetime import datetime

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from aristotlelib import Project, ProjectInputType, set_api_key, ProjectStatus

# Problems to submit (in priority order)
PROBLEMS = [
    ("03_erdos_discrepancy_C3_boris.txt", "erdos_discrepancy_C3_project_id.txt", "Erdős Discrepancy C=3"),
    ("02_R5_exact_boris.txt", "R5_exact_project_id.txt", "Ramsey R(5,5) Exact Value"),
    ("04_extremal_code_72_boris.txt", "extremal_code_72_project_id.txt", "Extremal Code [72,36,16]"),
    ("05_union_closed_N13_boris.txt", "union_closed_N13_project_id.txt", "Union-Closed N=13"),
    ("01_MOLS10_boris.txt", "MOLS10_project_id.txt", "Three MOLS Order 10"),
]

SUBMISSIONS_DIR = Path(__file__).resolve().parent


async def check_queue_status():
    """Check current queue status."""
    projects, _ = await Project.list_projects(limit=10)

    active = 0
    for p in projects:
        status = str(p.status)
        if "IN_PROGRESS" in status or "QUEUED" in status:
            active += 1

    return active, 5 - active


async def submit_problem(input_file: Path, id_file: Path, description: str):
    """Submit a single problem and save the project ID."""
    print(f"\n{'='*60}")
    print(f"Submitting: {description}")
    print(f"Input: {input_file.name}")
    print(f"{'='*60}")

    try:
        result = await Project.prove_from_file(
            input_file_path=str(input_file),
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False
        )

        # Extract project ID
        project_id = result if isinstance(result, str) else getattr(result, 'id', str(result))

        # Save ID
        with open(id_file, 'w') as f:
            f.write(f"{project_id}\n")
            f.write(f"# Problem: {description}\n")
            f.write(f"# Submitted: {datetime.now().isoformat()}\n")

        print(f"✅ SUCCESS: {project_id}")
        print(f"   ID saved to: {id_file.name}")

        return project_id

    except Exception as e:
        print(f"❌ FAILED: {e}")
        return None


async def main():
    # Get API key
    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        # Try reading from .zshrc
        zshrc = Path.home() / ".zshrc"
        if zshrc.exists():
            with open(zshrc) as f:
                for line in f:
                    if "ARISTOTLE_API_KEY" in line and "export" in line:
                        try:
                            api_key = line.split("=", 1)[1].strip().strip('"').strip("'")
                            break
                        except:
                            pass

    if not api_key:
        print("ERROR: ARISTOTLE_API_KEY not found")
        sys.exit(1)

    set_api_key(api_key)
    print("✅ API key configured")

    # Check queue
    print("\n📊 Checking queue status...")
    active, available = await check_queue_status()
    print(f"   Active projects: {active}/5")
    print(f"   Available slots: {available}")

    if available < len(PROBLEMS):
        print(f"\n⚠️  Only {available} slots available, will submit first {available} problems")
        problems_to_submit = PROBLEMS[:available]
    else:
        problems_to_submit = PROBLEMS

    if not problems_to_submit:
        print("\n❌ No slots available. Please wait for current projects to complete.")
        sys.exit(1)

    # Submit each problem
    submitted = []
    for input_name, id_name, description in problems_to_submit:
        input_file = SUBMISSIONS_DIR / input_name
        id_file = SUBMISSIONS_DIR / id_name

        if not input_file.exists():
            print(f"\n❌ File not found: {input_file}")
            continue

        project_id = await submit_problem(input_file, id_file, description)
        if project_id:
            submitted.append((description, project_id))

        # Brief pause between submissions
        await asyncio.sleep(2)

    # Summary
    print("\n" + "="*60)
    print("SUBMISSION SUMMARY")
    print("="*60)

    for desc, pid in submitted:
        print(f"✅ {desc}")
        print(f"   ID: {pid}")

    print(f"\nTotal submitted: {len(submitted)}/{len(problems_to_submit)}")
    print("\nMonitor progress at: https://aristotle.harmonic.fun")


if __name__ == "__main__":
    asyncio.run(main())
