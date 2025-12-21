#!/bin/bash
# Safe batch submission wrapper for Jones Unknotting Conjecture project
# Usage: ./submit_batch.sh <batch_name> <description>

set -e  # Exit on error

BATCH_NAME=$1
DESCRIPTION=$2

if [ -z "$BATCH_NAME" ] || [ -z "$DESCRIPTION" ]; then
    echo "Usage: ./submit_batch.sh <batch_name> <description>"
    echo ""
    echo "Example:"
    echo "  ./submit_batch.sh 9crossing_test 'First test batch: 10 knots at 9 crossings'"
    exit 1
fi

INPUT_FILE="unknotting/aristotle_batch_${BATCH_NAME}.txt"
ID_FILE="UNKNOTTING_${BATCH_NAME}_PROJECT_ID.txt"

echo "🚀 SUBMITTING BATCH: ${BATCH_NAME}"
echo "=================================================="
echo "Input:       ${INPUT_FILE}"
echo "ID file:     ${ID_FILE}"
echo "Description: ${DESCRIPTION}"
echo ""

# Check if input file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo "❌ Error: Input file not found: ${INPUT_FILE}"
    echo ""
    echo "Did you mean to run prepare_aristotle_batch.py first?"
    exit 1
fi

# Run safe submission
python3 safe_aristotle_submit.py \
    "$INPUT_FILE" \
    "$ID_FILE" \
    "$DESCRIPTION"

STATUS=$?

if [ $STATUS -eq 0 ]; then
    PROJECT_ID=$(head -1 "$ID_FILE")
    echo ""
    echo "✅ SUCCESS! Project submitted and running."
    echo "   Project ID: ${PROJECT_ID}"
    echo ""
    echo "📊 Next steps:"
    echo "   1. Monitor: python3 check_queue.py"
    echo "   2. Update GitHub: gh issue comment <issue_num> --body 'Submitted: ${PROJECT_ID}'"
    echo "   3. Wait for completion (~30min-2hr)"
else
    echo ""
    echo "❌ Submission failed with status ${STATUS}"
    echo "   Check logs above for details"
    exit $STATUS
fi
