#!/bin/bash
# PRD8: Post-result analysis and learning capture
# Usage: ./scripts/post_result.sh <uuid> <result_file>

set -e
UUID="${1:?Usage: $0 <uuid> <result_file>}"
RESULT_FILE="${2:?Usage: $0 <uuid> <result_file>}"
DB="submissions/tracking.db"

if [ ! -f "$RESULT_FILE" ]; then
    echo "ERROR: Result file not found: $RESULT_FILE"
    exit 1
fi

echo "════════════════════════════════════════════════════════════════"
echo "POST-RESULT ANALYSIS: $UUID"
echo "════════════════════════════════════════════════════════════════"

# 1. Count sorry statements
SORRY_COUNT=$(grep -c 'sorry' "$RESULT_FILE" 2>/dev/null || echo "0")
THEOREM_COUNT=$(grep -c -E '^(lemma|theorem)' "$RESULT_FILE" 2>/dev/null || echo "0")

echo ""
echo "▶ RESULT SUMMARY"
echo "────────────────────────────────────"
echo "Sorry count: $SORRY_COUNT"
echo "Theorem/lemma count: $THEOREM_COUNT"

# 2. Update submission record
sqlite3 "$DB" "
UPDATE submissions 
SET sorry_count = $SORRY_COUNT, 
    proven_count = $THEOREM_COUNT,
    output_file = '$RESULT_FILE',
    prior_work_checked = 1,
    completed_at = datetime('now')
WHERE uuid = '$UUID';
"

if [ "$SORRY_COUNT" -eq 0 ]; then
    echo ""
    echo "🎉 SUCCESS! Full proof achieved."
    echo ""
    echo "▶ EXTRACTING NEW PROVEN LEMMAS"
    echo "────────────────────────────────────"
    
    # Extract theorem names from successful proof
    grep -E '^(lemma|theorem)\s+\w+' "$RESULT_FILE" | awk '{print $2}' | while read name; do
        echo "Found: $name"
    done
    
    echo ""
    echo "Consider adding new lemmas to literature_lemmas with proof_status='proven'"
    
else
    echo ""
    echo "⚠ PARTIAL/FAILURE: $SORRY_COUNT sorry statements remain"
    echo ""
    echo "▶ DOCUMENT FAILURE FOR LEARNING"
    echo "────────────────────────────────────"
    
    # Get submission info
    PROBLEM_ID=$(sqlite3 "$DB" "SELECT problem_id FROM submissions WHERE uuid='$UUID';")
    FILENAME=$(sqlite3 "$DB" "SELECT filename FROM submissions WHERE uuid='$UUID';")
    
    echo "Problem ID: $PROBLEM_ID"
    echo "Filename: $FILENAME"
    echo ""
    
    # Check if running interactively
    if [ -t 0 ]; then
        read -p "Document this failure? (y/n): " DOCUMENT
        if [ "$DOCUMENT" = "y" ]; then
            read -p "Approach name (short): " APPROACH
            read -p "Why did it fail?: " WHY
            read -p "What did we learn? (insight): " INSIGHT
            read -p "What to avoid next time?: " AVOID
            
            # Escape single quotes for SQL
            APPROACH=$(echo "$APPROACH" | sed "s/'/''/g")
            WHY=$(echo "$WHY" | sed "s/'/''/g")
            INSIGHT=$(echo "$INSIGHT" | sed "s/'/''/g")
            AVOID=$(echo "$AVOID" | sed "s/'/''/g")
            
            sqlite3 "$DB" "
            INSERT INTO failed_approaches 
                (problem_id, submission_uuid, approach_name, approach_description, 
                 why_failed, learned_insight, avoid_pattern)
            VALUES 
                ('$PROBLEM_ID', '$UUID', '$APPROACH', 
                 'From submission $FILENAME', '$WHY', '$INSIGHT', '$AVOID');
            "
            echo ""
            echo "✓ Failure documented in failed_approaches table"
        fi
    else
        echo "Run interactively to document failure, or use:"
        echo "  sqlite3 $DB \"INSERT INTO failed_approaches ...\""
    fi
fi

echo ""
echo "════════════════════════════════════════════════════════════════"
echo "POST-RESULT ANALYSIS COMPLETE"
echo "════════════════════════════════════════════════════════════════"
