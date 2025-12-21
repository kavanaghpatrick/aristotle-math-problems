#!/bin/bash
# PRD8: Generate scaffolding Lean code for a submission
# Usage: ./scripts/get_scaffolding.sh [--full | --defs-only]

set -e
DB="submissions/tracking.db"
MODE="${1:---full}"

echo "-- Auto-generated scaffolding from literature database"
echo "-- Generated: $(date)"
echo ""

if [ "$MODE" = "--defs-only" ]; then
    # Just definitions
    sqlite3 "$DB" "
    SELECT statement FROM literature_lemmas 
    WHERE proof_status IN ('definition', 'proven') 
      AND type = 'definition'
      AND paper_id = 'parker2024'
    ORDER BY name;
    "
else
    # Full scaffolding with proofs
    echo "-- Definitions"
    sqlite3 "$DB" "
    SELECT statement FROM literature_lemmas 
    WHERE type = 'definition' AND paper_id = 'parker2024'
    ORDER BY name;
    "
    
    echo ""
    echo "-- Proven lemmas (include as axioms or full proofs)"
    sqlite3 "$DB" "
    SELECT '-- ' || name || ': ' || english FROM literature_lemmas 
    WHERE proof_status = 'proven' AND type != 'definition' AND paper_id = 'parker2024'
    ORDER BY name;
    "
fi
