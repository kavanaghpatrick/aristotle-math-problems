#!/bin/bash
# Monitor 25-crossing breakthrough batch

PROJECT_ID="4aef4bc7-ecf0-4e11-aab4-48da39ed3379"

echo "🔍 Monitoring 25-Crossing Breakthrough Batch"
echo "Project ID: $PROJECT_ID"
echo "=" * 70
echo

python3 << 'EOF'
import asyncio
from aristotlelib import Project, set_api_key

async def check():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")
    project = await Project.from_id("4aef4bc7-ecf0-4e11-aab4-48da39ed3379")
    await project.refresh()
    print(f"Status: {project.status}")
    print(f"Created: {project.created_at}")
    print(f"Updated: {project.updated_at}")

asyncio.run(check())
EOF
