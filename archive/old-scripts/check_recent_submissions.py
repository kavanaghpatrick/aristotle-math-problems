#!/usr/bin/env python3
"""Check recent Aristotle submissions for duplicates."""

import asyncio
from aristotlelib import Project, set_api_key
from datetime import datetime

async def check_recent():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    # Get recent projects
    projects, _ = await Project.list_projects(limit=15)

    print("🔍 RECENT ARISTOTLE SUBMISSIONS")
    print("=" * 80)
    print()

    # Show projects from last hour
    now = datetime.now()
    recent_ones = []

    for p in projects:
        created = datetime.fromisoformat(str(p.created_at).replace('Z', '+00:00'))
        age_minutes = (now - created.replace(tzinfo=None)).total_seconds() / 60

        if age_minutes < 60:  # Last hour
            recent_ones.append(p)
            # Use project_id instead of id
            project_id = getattr(p, 'project_id', getattr(p, 'id', 'unknown'))
            print(f"Project: {project_id}")
            print(f"  Status: {p.status}")
            print(f"  Created: {p.created_at} ({age_minutes:.1f} minutes ago)")
            print()

    if len(recent_ones) >= 2:
        print("⚠️  WARNING: Multiple projects submitted in last hour!")
        print(f"   Found {len(recent_ones)} recent submissions")
        print()
        print("   Checking if they might be duplicates...")
        print()

        # Check if they're close together
        times = [datetime.fromisoformat(str(p.created_at).replace('Z', '+00:00')) for p in recent_ones]
        times_sorted = sorted(times)

        for i in range(len(times_sorted) - 1):
            diff = (times_sorted[i+1] - times_sorted[i]).total_seconds()
            if diff < 60:  # Less than 1 minute apart
                print(f"   ⚠️  Two submissions {diff:.1f} seconds apart - likely duplicate!")

    elif len(recent_ones) == 1:
        print("✅ Only one recent submission in last hour")
        project_id = getattr(recent_ones[0], 'project_id', getattr(recent_ones[0], 'id', 'unknown'))
        print(f"   Project ID: {project_id}")

    else:
        print("ℹ️  No submissions in last hour")

asyncio.run(check_recent())
