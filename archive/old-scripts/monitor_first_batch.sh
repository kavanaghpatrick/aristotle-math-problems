#!/bin/bash
# Monitor first batch and alert when complete

PROJECT_ID="771e9804-7c02-4c86-b767-ac1b9f9742e1"

echo "🔍 MONITORING FIRST BATCH"
echo "Project ID: ${PROJECT_ID}"
echo "Started: ~01:04"
echo ""
echo "Press Ctrl+C to stop monitoring"
echo ""

while true; do
    STATUS=$(python3 -c "
import asyncio
from aristotlelib import Project, set_api_key

async def check():
    set_api_key('os.environ["ARISTOTLE_API_KEY"]')
    p = await Project.from_id('${PROJECT_ID}')
    await p.refresh()
    print(p.status)

asyncio.run(check())
" 2>/dev/null)

    TIMESTAMP=$(date '+%H:%M:%S')

    if [[ "$STATUS" == *"COMPLETE"* ]]; then
        echo "[$TIMESTAMP] ✅ COMPLETE! Batch finished!"
        echo ""
        echo "🎉 First batch is done! Next steps:"
        echo "   python3 download_and_analyze_batch.py ${PROJECT_ID}"
        osascript -e 'display notification "First batch complete!" with title "Aristotle"'
        exit 0
    elif [[ "$STATUS" == *"FAILED"* ]]; then
        echo "[$TIMESTAMP] ❌ FAILED! Check logs."
        osascript -e 'display notification "Batch failed!" with title "Aristotle"'
        exit 1
    else
        echo "[$TIMESTAMP] ⏳ ${STATUS}"
    fi

    sleep 60  # Check every minute
done
