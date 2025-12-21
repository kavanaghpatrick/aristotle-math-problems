#!/bin/bash
# Verify Aristotle output file
# Usage: ./scripts/verify_output.sh submissions/output/<uuid>.lean

set -euo pipefail

FILE="$1"
if [[ ! -f "$FILE" ]]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

echo "=== Aristotle Output Verification ==="
echo "File: $FILE"
echo

# 1. Sorry detection
echo "1. Checking for sorry statements..."
SORRY_COUNT=$(grep -c "sorry" "$FILE" 2>/dev/null || echo "0")
echo "   Found: $SORRY_COUNT"

if [[ $SORRY_COUNT -eq 0 ]]; then
    echo "   ✅ No sorry found - claimed PROVEN"
    CLAIMED_PROVEN=true
elif [[ $SORRY_COUNT -eq 1 ]]; then
    echo "   ⚠️  One sorry found - likely main theorem unsolved"
    grep -n "sorry" "$FILE" || true
    CLAIMED_PROVEN=false
else
    echo "   ⚠️  Multiple sorry found - partial proof"
    echo "   Locations:"
    grep -n "sorry" "$FILE" || true
    CLAIMED_PROVEN=false
fi

# 2. Axiom detection (should never be present)
echo
echo "2. Checking for axioms..."
if grep -q "^axiom \|^ *axiom " "$FILE"; then
    echo "   ❌ CRITICAL: File contains axioms (invalid proof)"
    grep -n "axiom" "$FILE" || true
    exit 1
else
    echo "   ✅ No axioms found"
fi

# 3. Compilation check (if claimed proven)
if [[ "$CLAIMED_PROVEN" = true ]]; then
    echo
    echo "3. Compiling claimed proof..."

    # Copy to test directory
    TEST_FILE="/tmp/verify_$(basename "$FILE")"
    cp "$FILE" "$TEST_FILE"

    if lake env lean "$TEST_FILE" 2>&1 | grep -q "error:"; then
        echo "   ❌ COMPILATION FAILED"
        lake env lean "$TEST_FILE" 2>&1 | grep "error:" | head -20
        exit 1
    else
        echo "   ✅ Compilation successful"
    fi

    # 4. Definition re-audit
    echo
    echo "4. Re-auditing definitions..."
    if ./scripts/audit_definitions.sh "$TEST_FILE"; then
        echo "   ✅ Definitions clean"
    else
        echo "   ⚠️  Definition issues found (see above)"
    fi

    rm "$TEST_FILE"
else
    echo
    echo "Skipping compilation (not claimed as proven)"
fi

# 5. Extract theorem claims
echo
echo "5. Extracting proven theorems..."
THEOREMS=$(grep "^theorem " "$FILE" | cut -d' ' -f2 | cut -d'(' -f1 || true)
if [[ -n "$THEOREMS" ]]; then
    echo "   Theorems found:"
    echo "$THEOREMS" | while read -r THM; do
        echo "   - $THM"
    done
else
    echo "   No theorems found"
fi

echo
echo "=== Verification Complete ==="

if [[ "$CLAIMED_PROVEN" = true ]]; then
    echo "✅ Output claims to be proven and passes basic verification"
    echo "   Recommend: Manual review + high-value problems should get multi-agent verification"
else
    echo "⚠️  Output is partial (contains sorry)"
    echo "   Status: Aristotle made progress but didn't complete proof"
fi

exit 0
