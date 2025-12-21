#!/bin/bash
# Find files with contaminated definitions
# Usage: ./scripts/find_contaminated.sh "coveringNumber" "sInf.*Sym2"

set -euo pipefail

DEF_NAME="$1"
BUG_PATTERN="$2"

echo "=== Contamination Search ==="
echo "Definition: $DEF_NAME"
echo "Bug pattern: $BUG_PATTERN"
echo

CONTAMINATED_FILES=()

# Search in submissions directory
for FILE in submissions/*.lean submissions/**/*.lean; do
    if [[ -f "$FILE" ]] && rg -q "def $DEF_NAME.*$BUG_PATTERN" "$FILE"; then
        echo "CONTAMINATED: $FILE"
        echo
        # Show the buggy definition
        rg -A 3 "def $DEF_NAME" "$FILE" || true
        echo
        echo "---"
        echo
        CONTAMINATED_FILES+=("$FILE")
    fi
done

echo
echo "=== Summary ==="
echo "Found ${#CONTAMINATED_FILES[@]} contaminated file(s)"

if [[ ${#CONTAMINATED_FILES[@]} -gt 0 ]]; then
    echo
    echo "Contaminated files:"
    printf '%s\n' "${CONTAMINATED_FILES[@]}"
    echo
    echo "Recommended actions:"
    echo "1. Review each file to confirm contamination"
    echo "2. Move to CORRUPTED directory:"
    echo "   mkdir -p submissions/CORRUPTED"
    for FILE in "${CONTAMINATED_FILES[@]}"; do
        echo "   git mv '$FILE' submissions/CORRUPTED/"
    done
    echo "3. Update database to mark as contaminated"
fi

exit 0
