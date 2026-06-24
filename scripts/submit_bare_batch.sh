#!/bin/bash
# Submit 5 bare (no-context) sketches to Aristotle v0.7.0
# Run this when the first batch completes and slots are available

set -e
cd "$(dirname "$0")/.."

echo "Submitting 5 bare sketches (no context — fresh eyes for v0.7.0)..."
echo ""

python3 scripts/safe_aristotle_submit.py --batch \
  submissions/sketches/erdos242_straus_bare.txt \
  submissions/sketches/erdos850_bare.txt \
  submissions/sketches/erdos389_consecutive_bare.txt \
  submissions/sketches/erdos672_l3_bare.txt \
  submissions/sketches/erdos203_covering_bare.txt

echo ""
echo "Done. Monitor with: aristotle list"
