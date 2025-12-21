#!/bin/bash
# Boris-Minimal Erdős Submission Script - Dec 19
# Re-ranked based on Aristotle capability analysis

cd /Users/patrickkavanagh/math/submissions

echo "=== Submitting Boris-Minimal Erdős Files ==="
echo "Mode: FORMAL_LEAN (Boris pattern - minimal, no comments)"
echo "Based on Aristotle capability re-ranking"
echo ""

# S-Tier: Highest confidence based on Aristotle's proven strengths

echo "S1. Submitting Erdős #128 ($250) - Graph theory sweet spot..."
aristotle prove-from-file erdos128_boris.lean --no-wait
echo ""

echo "S2. Submitting Erdős #931 - primeFactors (AlphaProof precedent)..."
aristotle prove-from-file erdos931_boris.lean --no-wait
echo ""

echo "S3. Submitting Erdős #939 ($3) - r-powerful (Cambie examples)..."
aristotle prove-from-file erdos939_boris.lean --no-wait
echo ""

echo "S4. Submitting Erdős #730 - centralBinom.primeFactors..."
aristotle prove-from-file erdos730_boris.lean --no-wait
echo ""

echo "A1. Submitting Erdős #313 - Primary pseudoperfect..."
aristotle prove-from-file erdos313_boris.lean --no-wait
echo ""

echo "=== All 5 submissions queued ==="
echo "Run 'aristotle list' to check progress"
echo "Expected runtime: 6-24 hours per problem"
echo ""
echo "Total prize potential: \$253"
