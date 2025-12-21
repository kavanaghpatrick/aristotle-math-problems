#!/bin/bash
# PRD8: Record which lemmas were scaffolded in a submission
# Usage: ./scripts/record_scaffolding.sh <submission_id> <lemma_id> <usage_type>

set -e
DB="submissions/tracking.db"

if [ "$#" -lt 3 ]; then
    echo "Usage: $0 <submission_id> <lemma_id> <usage_type>"
    echo ""
    echo "usage_type: full_proof | axiom | definition_only | statement_hint"
    echo ""
    echo "Available lemmas:"
    sqlite3 "$DB" "SELECT id, name FROM literature_lemmas WHERE proof_status='proven';"
    exit 1
fi

SUBMISSION_ID="$1"
LEMMA_ID="$2"
USAGE_TYPE="$3"

sqlite3 "$DB" "
INSERT OR REPLACE INTO submission_scaffolding 
    (submission_id, lemma_id, usage_type, effectiveness)
VALUES 
    ($SUBMISSION_ID, '$LEMMA_ID', '$USAGE_TYPE', 'unknown');
"

echo "✓ Recorded: submission $SUBMISSION_ID used $LEMMA_ID as $USAGE_TYPE"
