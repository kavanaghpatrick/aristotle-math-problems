#!/bin/bash
# Tuza ν=4 Portfolio v3 Submission Script
# Run when Aristotle slots are available

echo "=== Tuza ν=4 Portfolio v3 ==="
echo "7 slots designed from Gemini/Grok-4/Codex debate"
echo ""

FILES=(
    "submissions/tuza_nu4_v1_boris_prime.lean"      # Slot 1: Boris Prime (INFORMAL)
    "submissions/tuza_nu4_v1_boris_prime.md"        # Slot 1: Boris Prime informal text
    "submissions/tuza_nu4_v2_architect.lean"        # Slot 2: The Architect (FORMAL)
    "submissions/tuza_nu4_v3_surgeon.lean"          # Slot 3: The Surgeon (FORMAL)
    "submissions/tuza_nu4_v4_finite_check.lean"     # Slot 4: The Finite Check (FORMAL)
    "submissions/tuza_nu4_v5_conflict_graph.md"     # Slot 5: Conflict Graph (INFORMAL)
    "submissions/tuza_nu4_v6_pessimist.lean"        # Slot 6: The Pessimist (INFORMAL)
    "submissions/tuza_nu4_v7_slicer.lean"           # Slot 7: The Slicer (FORMAL)
)

echo "Submitting ${#FILES[@]} files..."
echo ""

python3 scripts/aristotle_queue.py "${FILES[@]}" --interval 60 --max-wait 7200

echo ""
echo "=== Submission Complete ==="
