#!/bin/bash
# Track a submission in the database
# Usage: ./scripts/track_submission.sh submissions/problem.lean "erdos128" "boris_minimal"

set -euo pipefail

FILE="$1"
PROBLEM_ID="${2:-unknown}"
PATTERN="${3:-unspecified}"

if [[ ! -f "$FILE" ]]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

DB="submissions/tracking.db"

echo "=== Submission Tracking ==="
echo "File: $FILE"
echo "Problem ID: $PROBLEM_ID"
echo "Pattern: $PATTERN"
echo

# Run validation
echo "Running validation..."
if ! ./scripts/validate_submission.sh "$FILE"; then
    echo
    echo "❌ Validation failed. Fix errors before submitting."
    exit 1
fi

# Run definition audit
echo
echo "Running definition audit..."
AUDIT_PASSED=0
if ./scripts/audit_definitions.sh "$FILE" > /tmp/audit_output.txt 2>&1; then
    AUDIT_PASSED=1
    echo "✅ Definitions audited: PASSED"
else
    if grep -q "CRITICAL" /tmp/audit_output.txt; then
        echo "❌ Definitions audited: FAILED"
        cat /tmp/audit_output.txt
        exit 1
    else
        echo "⚠️  Definitions audited: WARNINGS"
        AUDIT_PASSED=1
    fi
fi

# Generate pending UUID (to be replaced with actual Aristotle UUID)
UUID="pending_$(basename "$FILE" .lean)_$(date +%s)"

# Initialize database if needed
if [[ ! -f "$DB" ]]; then
    echo "Initializing database..."
    sqlite3 "$DB" << 'EOF'
CREATE TABLE IF NOT EXISTS submissions (
    uuid TEXT PRIMARY KEY,
    filename TEXT NOT NULL,
    submission_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    problem_id TEXT,
    status TEXT CHECK(status IN ('queued', 'running', 'completed', 'failed', 'timeout', 'pending')),
    pattern TEXT,
    validation_passed BOOLEAN DEFAULT 0,
    definitions_audited BOOLEAN DEFAULT 0,
    formalization_verified BOOLEAN DEFAULT 0,
    runtime_seconds INTEGER,
    result_file TEXT,
    notes TEXT
);

CREATE TABLE IF NOT EXISTS definitions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_uuid TEXT REFERENCES submissions(uuid),
    definition_name TEXT,
    definition_type TEXT,
    line_number INTEGER,
    audit_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(submission_uuid, definition_name)
);

CREATE TABLE IF NOT EXISTS proof_claims (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_uuid TEXT REFERENCES submissions(uuid),
    theorem_name TEXT,
    claim_status TEXT CHECK(claim_status IN ('proven', 'partial', 'sorry', 'contaminated')),
    verification_status TEXT CHECK(verification_status IN ('pending', 'verified', 'invalid')),
    sorry_count INTEGER DEFAULT 0,
    verification_date TIMESTAMP,
    invalidation_reason TEXT,
    UNIQUE(submission_uuid, theorem_name)
);

CREATE TABLE IF NOT EXISTS definition_contamination (
    source_uuid TEXT REFERENCES submissions(uuid),
    target_uuid TEXT REFERENCES submissions(uuid),
    contaminated_definition TEXT,
    discovered_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY(source_uuid, target_uuid, contaminated_definition)
);

CREATE INDEX IF NOT EXISTS idx_status ON submissions(status);
CREATE INDEX IF NOT EXISTS idx_problem ON submissions(problem_id);
CREATE INDEX IF NOT EXISTS idx_verification ON proof_claims(verification_status);
EOF
fi

# Record in database
sqlite3 "$DB" << EOF
INSERT INTO submissions (uuid, filename, problem_id, status, pattern, validation_passed, definitions_audited)
VALUES ('$UUID', '$FILE', '$PROBLEM_ID', 'pending', '$PATTERN', 1, $AUDIT_PASSED);
EOF

echo
echo "✅ Submission recorded in database"
echo "   UUID: $UUID"
echo
echo "Next steps:"
echo "1. Submit to Aristotle:"
echo "   aristotle prove-from-file $FILE --no-wait"
echo
echo "2. Update database with actual UUID:"
echo "   ./scripts/update_uuid.sh $UUID <actual_aristotle_uuid>"
echo

exit 0
