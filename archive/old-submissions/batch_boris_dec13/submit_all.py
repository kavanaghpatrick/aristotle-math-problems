#!/usr/bin/env python3
"""
Batch submission script for Boris-pattern problems to Aristotle.
Submits all .txt files in this directory using --informal mode.
"""

import asyncio
import os
import sys
from pathlib import Path
from datetime import datetime

# Add parent directory to path for safe_aristotle_submit
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "scripts"))

try:
    from aristotlelib import Project, ProjectInputType, set_api_key
except ImportError:
    print("ERROR: aristotlelib not installed. Run: pip install aristotlelib")
    sys.exit(1)

# Submission order based on Grok's analysis (highest success probability first)
SUBMISSION_ORDER = [
    ("erdos_023_triangle_free_bipartite.txt", "Erdős #23: Triangle-free → bipartite"),
    ("erdos_152_sidon_gaps.txt", "Erdős #152: Sidon sumset gaps"),
    ("erdos_153_sidon_variance.txt", "Erdős #153: Sidon variance → ∞"),
    ("erdos_190_rainbow_ap.txt", "Erdős #190: Rainbow vs mono AP"),
    ("erdos_149_strongly_independent_edges.txt", "Erdős #149: Strongly independent edges"),
    ("erdos_167_triangle_removal.txt", "Erdős #167: Triangle removal bound"),
    ("erdos_593_hypergraph_characterization.txt", "Erdős #593: 3-hypergraph characterization ($500)"),
]

async def submit_problem(filepath: Path, description: str) -> tuple[str, str]:
    """Submit a single problem to Aristotle."""
    print(f"\n{'='*60}")
    print(f"Submitting: {description}")
    print(f"File: {filepath.name}")
    print(f"{'='*60}")

    try:
        project = await Project.prove_from_file(
            input_file_path=str(filepath),
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False  # Don't wait - just queue it
        )

        project_id = project.project_id
        print(f"✅ Submitted! Project ID: {project_id}")

        # Save project ID
        id_file = filepath.with_suffix('.project_id.txt')
        with open(id_file, 'w') as f:
            f.write(f"{project_id}\n")
            f.write(f"Submitted: {datetime.now().isoformat()}\n")
            f.write(f"Description: {description}\n")

        return filepath.name, project_id

    except Exception as e:
        print(f"❌ Failed: {e}")
        return filepath.name, f"ERROR: {e}"

async def main():
    # Set API key
    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        print("ERROR: ARISTOTLE_API_KEY not set")
        sys.exit(1)
    set_api_key(api_key)

    # Get directory
    script_dir = Path(__file__).parent

    print("=" * 60)
    print("BORIS-PATTERN BATCH SUBMISSION")
    print(f"Directory: {script_dir}")
    print(f"Time: {datetime.now().isoformat()}")
    print("=" * 60)

    results = []

    for filename, description in SUBMISSION_ORDER:
        filepath = script_dir / filename
        if filepath.exists():
            name, result = await submit_problem(filepath, description)
            results.append((name, result))
            # Small delay between submissions to be nice to the API
            await asyncio.sleep(2)
        else:
            print(f"⚠️  Skipping {filename} - file not found")

    # Summary
    print("\n" + "=" * 60)
    print("SUBMISSION SUMMARY")
    print("=" * 60)
    for name, result in results:
        status = "✅" if not result.startswith("ERROR") else "❌"
        print(f"{status} {name}: {result[:50]}...")

    # Save summary
    summary_file = script_dir / "submission_summary.txt"
    with open(summary_file, 'w') as f:
        f.write(f"Batch Submission Summary\n")
        f.write(f"Time: {datetime.now().isoformat()}\n")
        f.write(f"{'='*60}\n\n")
        for name, result in results:
            f.write(f"{name}: {result}\n")

    print(f"\nSummary saved to: {summary_file}")

if __name__ == "__main__":
    asyncio.run(main())
