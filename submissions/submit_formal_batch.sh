#!/bin/bash
# Formal Lean Submission Script - Dec 14
# Uses FORMAL_LEAN mode (not INFORMAL) to prevent Aristotle from redefining the problem

# Change to submissions directory
cd /Users/patrickkavanagh/math/submissions/batch_dec14_precise

echo "=== Submitting Precise Formal Files ==="
echo "Mode: FORMAL_LEAN (fills sorries exactly)"
echo ""

# Submit each file in FORMAL mode (no --informal flag)
echo "1. Submitting Erdős #1052 (Unitary Perfect Numbers)..."
aristotle prove-from-file erdos1052_precise.lean --no-wait
echo ""

echo "2. Submitting Erdős #939 (r-Powerful Sums)..."
aristotle prove-from-file erdos939_precise.lean --no-wait
echo ""

echo "3. Submitting Erdős #647 (τ(n) + n bound)..."
aristotle prove-from-file erdos647_precise.lean --no-wait
echo ""

echo "4. Submitting Erdős #1059 (Factorial Subtractions)..."
aristotle prove-from-file erdos1059_precise.lean --no-wait
echo ""

echo "=== All submissions queued ==="
echo "Run 'aristotle status' to check progress"
echo "Expected runtime: 6-24 hours per problem"
