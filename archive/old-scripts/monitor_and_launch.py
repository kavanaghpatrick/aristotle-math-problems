#!/usr/bin/env python3
"""
Monitor Aristotle queue and auto-launch Quantum Query v2 when slot opens
"""
import asyncio
import time
from aristotlelib import Project, ProjectStatus, ProjectInputType, set_api_key

async def monitor_queue_and_launch():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🔍 Monitoring Aristotle queue for available slot...")
    print("📋 Ready to launch: Quantum Query v2 (highest priority)")
    print("⏳ Expected slot opening: ~10-15 minutes\n")

    launched = False
    check_count = 0

    while not launched:
        check_count += 1
        projects, _ = await Project.list_projects(limit=10)

        # Count running/queued projects
        active = [p for p in projects if p.status in [ProjectStatus.QUEUED, ProjectStatus.IN_PROGRESS]]
        slots_used = len(active)

        timestamp = time.strftime("%H:%M:%S")
        print(f"[{timestamp}] Check #{check_count}: {slots_used}/5 slots used", end="")

        if slots_used < 5:
            print(" ✅ SLOT AVAILABLE!")
            print("\n🚀 Launching Quantum Query v2...")

            project_id = await Project.prove_from_file(
                input_file_path="/Users/patrickkavanagh/math/quantum_query_v2_with_context.txt",
                project_input_type=ProjectInputType.INFORMAL,
                wait_for_completion=False
            )

            print(f"\n✅ SUCCESS! Quantum Query v2 launched")
            print(f"📍 Project ID: {project_id}")
            print(f"🎯 Goal: Complete polynomial_bound_holds proof")
            print(f"📊 Success probability: 40-60% (per Grok-4)")
            print(f"⏱️  Expected timeline: 3-7 days with iterations")

            # Save project ID for tracking
            with open("/Users/patrickkavanagh/math/QUANTUM_V2_PROJECT_ID.txt", "w") as f:
                f.write(f"Project ID: {project_id}\n")
                f.write(f"Launched: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"Goal: Prove polynomial_bound_holds for d<6\n")

            launched = True
        else:
            print(" - waiting...")
            # Show which projects are running
            if check_count % 5 == 1:  # Every 5th check, show details
                print("\n  Running projects:")
                for p in active[:5]:
                    print(f"    - {p.project_id} ({p.status.name})")

            # Wait 60 seconds before next check
            await asyncio.sleep(60)

    print("\n✨ Monitoring complete - Quantum Query v2 is now running!")

if __name__ == "__main__":
    asyncio.run(monitor_queue_and_launch())
