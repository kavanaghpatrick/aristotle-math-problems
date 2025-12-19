#!/bin/bash
# Validate a Lean submission file before sending to Aristotle
# Usage: ./scripts/validate_submission.sh submissions/file.lean

set -e

FILE="$1"

if [ -z "$FILE" ]; then
    echo "Usage: $0 <file.lean>"
    exit 1
fi

if [ ! -f "$FILE" ]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

echo "Validating: $FILE"

# Create temporary validation file
TEMP_FILE=$(mktemp /tmp/validate_XXXXXX.lean)
cp "$FILE" "$TEMP_FILE"

# Run lean to check syntax and types
cd /Users/patrickkavanagh/math

# Check if Mathlib cache exists
if [ ! -d ".lake/packages/mathlib" ]; then
    echo "Mathlib not found. Running 'lake update' first..."
    lake update
    echo "Downloading Mathlib cache (this may take a few minutes first time)..."
    lake exe cache get
fi

# Validate the file
echo "Running: lake env lean $TEMP_FILE"
if lake env lean "$TEMP_FILE" 2>&1; then
    echo "✓ Validation PASSED: $FILE"
    rm "$TEMP_FILE"
    exit 0
else
    echo "✗ Validation FAILED: $FILE"
    rm "$TEMP_FILE"
    exit 1
fi
