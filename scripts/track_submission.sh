#!/bin/bash
# Track a submission in the database
# Usage: ./scripts/track_submission.sh submissions/problem.lean "problem_id" "pattern" ["novelty_level"] ["contribution_statement"]
#
# novelty_level: discovery | extension | new_technique | formalization | duplication
# contribution_statement: "What's new if this succeeds"

set -euo pipefail

FILE="$1"
PROBLEM_ID="${2:-unknown}"
PATTERN="${3:-boris_minimal}"
NOVELTY_LEVEL="${4:-}"
CONTRIBUTION="${5:-}"

if [[ ! -f "$FILE" ]]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

DB="submissions/tracking.db"

echo "=== Submission Tracking ==="
echo "File: $FILE"
echo "Problem ID: $PROBLEM_ID"
echo "Pattern: $PATTERN"
if [[ -n "$NOVELTY_LEVEL" ]]; then
    echo "Novelty Level: $NOVELTY_LEVEL"
fi
if [[ -n "$CONTRIBUTION" ]]; then
    echo "Contribution: $CONTRIBUTION"
fi
echo

# Validate novelty level if provided
if [[ -n "$NOVELTY_LEVEL" ]]; then
    case "$NOVELTY_LEVEL" in
        discovery|extension|new_technique|formalization|duplication)
            ;;
        *)
            echo "⚠️  Warning: Unknown novelty level '$NOVELTY_LEVEL'"
            echo "   Valid: discovery, extension, new_technique, formalization, duplication"
            ;;
    esac
fi

# Run validation if script exists
if [[ -x "./scripts/validate_submission.sh" ]]; then
    echo "Running validation..."
    if ! ./scripts/validate_submission.sh "$FILE"; then
        echo
        echo "❌ Validation failed. Fix errors before submitting."
        exit 1
    fi
else
    echo "⚠️  Validation script not found, skipping..."
fi

# Run definition audit if script exists
AUDIT_PASSED=1
if [[ -x "./scripts/audit_definitions.sh" ]]; then
    echo
    echo "Running definition audit..."
    if ./scripts/audit_definitions.sh "$FILE" > /tmp/audit_output.txt 2>&1; then
        echo "✅ Definitions audited: PASSED"
    else
        if grep -q "CRITICAL" /tmp/audit_output.txt 2>/dev/null; then
            echo "❌ Definitions audited: FAILED"
            cat /tmp/audit_output.txt
            AUDIT_PASSED=0
        else
            echo "⚠️  Definitions audited: WARNINGS"
        fi
    fi
fi

# Generate UUID
UUID=$(uuidgen | tr '[:upper:]' '[:lower:]')

# Escape single quotes in contribution statement
CONTRIBUTION_ESCAPED=$(echo "$CONTRIBUTION" | sed "s/'/''/g")

# Record in database
sqlite3 "$DB" << EOF
INSERT OR REPLACE INTO submissions (
    uuid, filename, problem_id, pattern, status,
    syntax_valid, definition_audit_passed,
    novelty_level, contribution_statement, prior_work_checked,
    created_at
) VALUES (
    '$UUID',
    '$FILE',
    '$PROBLEM_ID',
    '$PATTERN',
    'draft',
    1,
    $AUDIT_PASSED,
    $([ -n "$NOVELTY_LEVEL" ] && echo "'$NOVELTY_LEVEL'" || echo "NULL"),
    $([ -n "$CONTRIBUTION_ESCAPED" ] && echo "'$CONTRIBUTION_ESCAPED'" || echo "NULL"),
    $([ -n "$NOVELTY_LEVEL" ] && echo "1" || echo "0"),
    datetime('now')
);
EOF

echo
echo "✅ Submission tracked in database"
echo "   UUID: $UUID"
echo "   File: $FILE"
echo

# Remind about novelty if not provided
if [[ -z "$NOVELTY_LEVEL" ]]; then
    echo "💡 Consider adding novelty level:"
    echo "   sqlite3 $DB \"UPDATE submissions SET novelty_level='discovery', contribution_statement='...' WHERE uuid='$UUID';\""
    echo
fi

echo "Next steps:"
echo "1. Submit to Aristotle:"
echo "   aristotle prove-from-file $FILE --no-wait"
echo
echo "2. Update with Aristotle UUID:"
echo "   sqlite3 $DB \"UPDATE submissions SET uuid='<aristotle_uuid>', status='running' WHERE uuid='$UUID';\""
echo

exit 0
