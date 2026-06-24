#!/bin/bash
# Session start hook — injects orchestrator queue status + Aristotle job status

MATH_DIR="$(cd "$(dirname "$0")/.." && pwd)"
DB="$MATH_DIR/submissions/tracking.db"

echo "=== PROOF ORCHESTRATOR QUEUE ==="

# Queue status
if [ -f "$DB" ]; then
    # Check if proof_queue table exists
    HAS_TABLE=$(sqlite3 "$DB" "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='proof_queue';" 2>/dev/null)
    if [ "$HAS_TABLE" = "1" ]; then
        ACTIVE=$(sqlite3 "$DB" "SELECT COUNT(*) FROM proof_queue WHERE state NOT IN ('RESOLVED','STALLED');" 2>/dev/null)
        RESOLVED=$(sqlite3 "$DB" "SELECT COUNT(*) FROM proof_queue WHERE state = 'RESOLVED';" 2>/dev/null)
        STALLED=$(sqlite3 "$DB" "SELECT COUNT(*) FROM proof_queue WHERE state = 'STALLED';" 2>/dev/null)
        echo "Active: $ACTIVE | Resolved: $RESOLVED | Stalled: $STALLED"

        # Show active items
        if [ "$ACTIVE" -gt 0 ] 2>/dev/null; then
            echo ""
            sqlite3 -header -column "$DB" \
                "SELECT id, problem_id, state, codex_attempts as cx, aristotle_rounds as ar, best_sorry_count as sorry
                 FROM proof_queue
                 WHERE state NOT IN ('RESOLVED','STALLED')
                 ORDER BY priority ASC, created_at ASC;" 2>/dev/null
        fi
    else
        echo "No proof_queue table yet. Run: python3 scripts/proof_orchestrator.py enqueue <problem>"
    fi
else
    echo "No tracking DB found."
fi

echo ""
echo "=== PENDING ACTIONS ==="

# Check for Aristotle jobs that might be done
if [ -f "$DB" ]; then
    ARISTOTLE_PENDING=$(sqlite3 "$DB" "SELECT COUNT(*) FROM proof_queue WHERE state IN ('ARISTOTLE_SUBMITTED','ARISTOTLE_RUNNING');" 2>/dev/null || echo 0)
    QUEUED=$(sqlite3 "$DB" "SELECT COUNT(*) FROM proof_queue WHERE state = 'QUEUED';" 2>/dev/null || echo 0)

    if [ "$ARISTOTLE_PENDING" -gt 0 ] 2>/dev/null; then
        echo "- $ARISTOTLE_PENDING Aristotle job(s) to poll — run orchestrator to check"
    fi
    if [ "$QUEUED" -gt 0 ] 2>/dev/null; then
        echo "- $QUEUED problem(s) queued for Codex — run orchestrator to process"
    fi
    if [ "$ARISTOTLE_PENDING" = "0" ] && [ "$QUEUED" = "0" ]; then
        echo "- Queue empty. Enqueue problems or run /sweep to find open gaps."
    fi
fi

echo ""
echo "Commands: orchestrator run | orchestrator status | enqueue <problem> | /codex-prove <problem>"
