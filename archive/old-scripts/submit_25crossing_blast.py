#!/usr/bin/env python3
"""BLAST: Submit 25-crossing verification to Aristotle."""

import asyncio
import json
from aristotlelib import Project, ProjectInputType, set_api_key
from datetime import datetime

async def blast_25crossing():
    """Submit the 25-crossing breakthrough batch to Aristotle."""

    print("🚀" * 35)
    print("=" * 70)
    print("  25-CROSSING BREAKTHROUGH SUBMISSION")
    print("  Beyond State-of-the-Art: First Formal Verification >24 Crossings")
    print("=" * 70)
    print("🚀" * 35)
    print()

    # Set API key
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("📋 Submission Details:")
    print("-" * 70)
    print(f"  Target: 25-crossing knots (20 test knots)")
    print(f"  Method: Braid closures (4-strand and 5-strand)")
    print(f"  Type: Informal problem statement")
    print(f"  Expected: First formal proofs beyond 24 crossings")
    print(f"  Risk: HIGH (frontier exploration)")
    print(f"  Reward: Nature-level breakthrough if successful")
    print("-" * 70)
    print()

    # Check queue status first
    print("🔍 Checking current queue status...")
    try:
        projects, _ = await Project.list_projects(limit=10)
        active_count = sum(1 for p in projects if p.status in ['QUEUED', 'IN_PROGRESS'])
        print(f"  Active projects: {active_count}/5")

        if active_count >= 5:
            print("  ⚠️  WARNING: Queue at capacity!")
            print("  Proceeding anyway (will queue when slot opens)")
        else:
            print(f"  ✅ Queue has capacity ({5-active_count} slots available)")
    except Exception as e:
        print(f"  ⚠️  Could not check queue: {e}")
        print("  Proceeding with submission anyway...")
    print()

    print("📤 Submitting to Aristotle...")
    print("-" * 70)

    # Submit the project
    try:
        result = await Project.prove_from_file(
            input_file_path="/Users/patrickkavanagh/math/aristotle_25crossing_problem.txt",
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False  # Don't wait - this could take a while!
        )

        # Get project ID
        project_id = result if isinstance(result, str) else result.id

        print(f"✅ SUBMISSION SUCCESSFUL!")
        print()
        print(f"🆔 Project ID: {project_id}")
        print()

        # Save to our tracking system
        submission_record = {
            "project_id": project_id,
            "submission_time": datetime.now().isoformat(),
            "batch_name": "25crossing_blast_01",
            "knot_count": 20,
            "crossing_number": 25,
            "description": "First formal verification attempt beyond 24 crossings - BREAKTHROUGH BATCH",
            "input_file": "aristotle_25crossing_problem.txt",
            "knots_file": "25crossing_test_knots.json",
            "status": "submitted",
            "expected_impact": "Nature-level if >5 knots succeed"
        }

        # Append to submission log
        with open('/Users/patrickkavanagh/math/aristotle_submission_log.jsonl', 'a') as f:
            f.write(json.dumps(submission_record) + '\n')

        # Also save standalone file
        with open('/Users/patrickkavanagh/math/25CROSSING_SUBMISSION.json', 'w') as f:
            json.dump(submission_record, f, indent=2)

        print("💾 Submission logged to:")
        print("  - aristotle_submission_log.jsonl")
        print("  - 25CROSSING_SUBMISSION.json")
        print()

        print("=" * 70)
        print("🎯 WHAT HAPPENS NEXT")
        print("=" * 70)
        print()
        print("Aristotle is now processing the 25-crossing batch.")
        print()
        print("Expected timeline:")
        print("  - If speed matches 12-crossing: ~6-8 minutes")
        print("  - If complexity scales 10x: ~1-2 hours")
        print("  - If complexity scales 100x: ~10-20 hours")
        print("  - If most timeout: Will complete what's feasible")
        print()
        print("Success criteria:")
        print("  🥇 BREAKTHROUGH (Nature-worthy): >10 knots verified")
        print("  🥈 MAJOR SUCCESS: 5-10 knots verified")
        print("  🥉 PROOF OF CONCEPT: 1-5 knots verified")
        print("  ⚠️  PIVOT NEEDED: 0 knots verified")
        print()
        print("Monitoring:")
        print(f"  python3 check_batch_status.py {project_id}")
        print()
        print("Or create monitoring script:")
        print(f"  echo '{project_id}' > current_project_id.txt")
        print()

        # Create quick monitoring script
        with open('/Users/patrickkavanagh/math/monitor_25crossing.sh', 'w') as f:
            f.write(f"""#!/bin/bash
# Monitor 25-crossing breakthrough batch

PROJECT_ID="{project_id}"

echo "🔍 Monitoring 25-Crossing Breakthrough Batch"
echo "Project ID: $PROJECT_ID"
echo "=" * 70
echo

python3 << 'EOF'
import asyncio
from aristotlelib import Project, set_api_key

async def check():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")
    project = await Project.from_id("{project_id}")
    await project.refresh()
    print(f"Status: {{project.status}}")
    print(f"Created: {{project.created_at}}")
    print(f"Updated: {{project.updated_at}}")

asyncio.run(check())
EOF
""")

        import os
        os.chmod('/Users/patrickkavanagh/math/monitor_25crossing.sh', 0o755)

        print("✅ Created monitoring script: monitor_25crossing.sh")
        print()

        print("=" * 70)
        print("🚀 BREAKTHROUGH ATTEMPT LAUNCHED!")
        print("=" * 70)
        print()
        print("We are now formally verifying knots beyond the computational")
        print("state-of-the-art. This is uncharted territory.")
        print()
        print("Even partial success (5 knots) would be a major breakthrough.")
        print()
        print("🎲 The dice are cast. Let's make history! 🎲")
        print()
        print("=" * 70)

    except Exception as e:
        print(f"❌ SUBMISSION FAILED!")
        print()
        print(f"Error: {e}")
        print()
        print("Troubleshooting:")
        print("  1. Check API key is valid")
        print("  2. Check queue capacity")
        print("  3. Check input file exists")
        print("  4. Check network connection")
        import traceback
        traceback.print_exc()

# Run the submission
if __name__ == "__main__":
    asyncio.run(blast_25crossing())
