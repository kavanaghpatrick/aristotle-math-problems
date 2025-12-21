#!/bin/bash
# Pre-submission validation for Lean files
# Usage: ./scripts/validate_submission.sh submissions/problem.lean

set -euo pipefail

FILE="$1"
if [[ ! -f "$FILE" ]]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

echo "=== Pre-Submission Validation ==="
echo "File: $FILE"
echo

# Run from math directory
cd /Users/patrickkavanagh/math

# Check if Mathlib cache exists
if [ ! -d ".lake/packages/mathlib" ]; then
    echo "Mathlib not found. Running 'lake update' first..."
    lake update
    echo "Downloading Mathlib cache (this may take a few minutes first time)..."
    lake exe cache get
fi

# 1. Syntax check
echo "1. Syntax and type checking..."
LEAN_OUTPUT=$(lake env lean "$FILE" 2>&1 || true)

# Filter out expected sorry warnings
ERRORS=$(echo "$LEAN_OUTPUT" | grep "error:" || true)

if [[ -n "$ERRORS" ]]; then
    echo "❌ FAILED: Syntax/type errors found"
    echo "$ERRORS"
    exit 1
else
    echo "✅ PASSED: No syntax errors"
fi

# 2. Definition audit
echo
echo "2. Definition audit..."
if [[ -f "./scripts/audit_definitions.sh" ]]; then
    if ./scripts/audit_definitions.sh "$FILE"; then
        echo "✅ PASSED: Definitions clean"
    else
        echo "❌ FAILED: Definition audit failed"
        exit 1
    fi
else
    echo "⚠️  WARNING: audit_definitions.sh not found, skipping"
fi

# 3. Sorry count
echo
echo "3. Sorry count..."
SORRY_COUNT=$(grep -c "sorry" "$FILE" 2>/dev/null || echo "0")
echo "Found $SORRY_COUNT sorry statements (expected for submission)"

# 4. Required imports
echo
echo "4. Checking required imports..."
if ! grep -q "^import Mathlib" "$FILE"; then
    echo "⚠️  WARNING: No 'import Mathlib' found"
fi

# 5. Required instances
echo
echo "5. Checking instances..."
MISSING_INSTANCES=()
if ! grep -q "\[Fintype V\]" "$FILE"; then
    MISSING_INSTANCES+=("Fintype V")
fi
if ! grep -q "\[DecidableEq V\]" "$FILE"; then
    MISSING_INSTANCES+=("DecidableEq V")
fi

if [[ ${#MISSING_INSTANCES[@]} -gt 0 ]]; then
    echo "⚠️  WARNING: Potentially missing instances: ${MISSING_INSTANCES[*]}"
    echo "   (This is OK if they're inherited from other variables)"
else
    echo "✅ Common instances found"
fi

echo
echo "=== VALIDATION COMPLETE ==="
echo "✅ SAFE TO SUBMIT"
exit 0
