#!/bin/bash
# PRD8: Pre-submission validation and scaffolding recommendation
# Usage: ./scripts/pre_submit.sh submissions/file.lean

set -e
LEAN_FILE="${1:?Usage: $0 <lean_file>}"
DB="submissions/tracking.db"

if [ ! -f "$LEAN_FILE" ]; then
    echo "ERROR: File not found: $LEAN_FILE"
    exit 1
fi

echo "════════════════════════════════════════════════════════════════"
echo "PRE-SUBMISSION CHECK: $LEAN_FILE"
echo "════════════════════════════════════════════════════════════════"

# 1. Extract lemma/theorem names used in submission
echo ""
echo "▶ DEFINITIONS AND LEMMAS REFERENCED"
echo "────────────────────────────────────"
USED_NAMES=$(grep -oE '(lemma|theorem|def|structure)\s+\w+' "$LEAN_FILE" 2>/dev/null | awk '{print $2}' | sort -u || true)
if [ -n "$USED_NAMES" ]; then
    echo "$USED_NAMES" | head -20
else
    echo "(none found)"
fi

# 2. Check against our proven lemmas
echo ""
echo "▶ MATCHING PROVEN LEMMAS IN DATABASE"
echo "────────────────────────────────────"
sqlite3 "$DB" "
SELECT ll.name, '(' || ll.proof_status || ')' as status, substr(ll.english, 1, 50) as description
FROM literature_lemmas ll
WHERE ll.proof_status = 'proven'
ORDER BY ll.name;
" | head -20

# 3. Scaffolding recommendations based on effectiveness history
echo ""
echo "▶ RECOMMENDED SCAFFOLDING (by past effectiveness)"
echo "────────────────────────────────────"
sqlite3 "$DB" "
SELECT ll.name, 
       COALESCE(SUM(CASE WHEN ss.effectiveness='essential' THEN 2 
                        WHEN ss.effectiveness='helpful' THEN 1 
                        ELSE 0 END), 0) as score,
       ll.english
FROM literature_lemmas ll
LEFT JOIN submission_scaffolding ss ON ll.id = ss.lemma_id
WHERE ll.proof_status = 'proven'
GROUP BY ll.id
ORDER BY score DESC
LIMIT 10;
"

# 4. Check for similar past failures
echo ""
echo "▶ PAST FAILURES TO AVOID"
echo "────────────────────────────────────"
sqlite3 "$DB" "
SELECT approach_name, 
       '⚠ ' || substr(why_failed, 1, 60) as warning,
       '→ ' || substr(avoid_pattern, 1, 60) as avoid
FROM failed_approaches 
ORDER BY created_at DESC 
LIMIT 5;
"

# 5. Axiom risk check
echo ""
echo "▶ LOW-CONFIDENCE AXIOMS (folklore/should_prove)"
echo "────────────────────────────────────"
LOW_CONF=$(sqlite3 "$DB" "
SELECT ll.name, ll.axiom_confidence 
FROM literature_lemmas ll
WHERE ll.axiom_confidence IN ('folklore', 'should_prove');
")
if [ -n "$LOW_CONF" ]; then
    echo "$LOW_CONF"
    echo ""
    echo "⚠ WARNING: Using these axioms adds risk to your proof"
else
    echo "(none - all axioms are peer-reviewed or higher)"
fi

# 6. Dependency check for key lemmas
echo ""
echo "▶ TRANSITIVE DEPENDENCIES FOR tau_S_le_2"
echo "────────────────────────────────────"
sqlite3 "$DB" "
WITH RECURSIVE deps AS (
    SELECT depends_on_id as id, 1 as depth
    FROM lemma_dependencies WHERE lemma_id = 'parker2024_tau_S_le_2'
    UNION ALL
    SELECT ld.depends_on_id, d.depth + 1
    FROM lemma_dependencies ld
    JOIN deps d ON ld.lemma_id = d.id
    WHERE d.depth < 5
)
SELECT DISTINCT ll.name, ll.proof_status
FROM deps d
JOIN literature_lemmas ll ON d.id = ll.id
ORDER BY ll.name;
"

echo ""
echo "════════════════════════════════════════════════════════════════"
echo "PRE-SUBMISSION CHECK COMPLETE"
echo "════════════════════════════════════════════════════════════════"
