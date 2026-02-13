#!/usr/bin/env bash
# SessionStart hook: Generate ~300 token briefing from tracking.db + knowledge.db
set -uo pipefail

PLUGIN_ROOT="${CLAUDE_PLUGIN_ROOT:-$(dirname "$0")/../..}"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(cd "$PLUGIN_ROOT/.." && pwd)}"
TRACKING_DB="${PROJECT_DIR}/submissions/tracking.db"
KNOWLEDGE_DB="${PLUGIN_ROOT}/data/knowledge.db"

# Initialize knowledge.db if missing
if [[ ! -f "$KNOWLEDGE_DB" ]]; then
    sqlite3 "$KNOWLEDGE_DB" < "${PLUGIN_ROOT}/data/schema.sql" 2>/dev/null || true
fi

# Helper: run sqlite3 query, return empty string on failure
q() {
    sqlite3 "$1" "$2" 2>/dev/null || echo ""
}

# ---- Gather data from tracking.db ----
TOTAL_SUBMISSIONS=$(q "$TRACKING_DB" "SELECT COUNT(*) FROM submissions;")
IN_FLIGHT=$(q "$TRACKING_DB" "SELECT COUNT(*) FROM submissions WHERE status IN ('submitted','running');")
COMPLETED_UNFETCHED=$(q "$TRACKING_DB" \
    "SELECT GROUP_CONCAT('slot' || CAST(SUBSTR(filename, 5, INSTR(SUBSTR(filename,5),'_')-1) AS INTEGER), ', ')
     FROM submissions
     WHERE status = 'completed' AND verified IS NULL
     AND completed_at > datetime('now', '-48 hours')
     ORDER BY completed_at DESC LIMIT 5;")
SLOTS_OPEN=$((5 - ${IN_FLIGHT:-0}))
if [[ $SLOTS_OPEN -lt 0 ]]; then SLOTS_OPEN=0; fi

RECENT_PROVEN=$(q "$TRACKING_DB" \
    "SELECT GROUP_CONCAT(filename || ' (' || proven_count || ' theorems)', ', ')
     FROM submissions
     WHERE verified = 1 AND sorry_count = 0
     AND completed_at > datetime('now', '-7 days')
     ORDER BY completed_at DESC LIMIT 3;")

NEAR_MISS=$(q "$TRACKING_DB" \
    "SELECT filename || ' (' || sorry_count || ' sorry, ' || proven_count || ' proven)'
     FROM submissions
     WHERE status = 'completed' AND sorry_count = 1 AND proven_count > 5
     ORDER BY proven_count DESC LIMIT 1;")

# ---- Gather data from knowledge.db ----
KB_COUNT=$(q "$KNOWLEDGE_DB" "SELECT COUNT(*) FROM findings;" 2>/dev/null || echo "0")
KB_RECENT=$(q "$KNOWLEDGE_DB" \
    "SELECT title FROM findings ORDER BY created_at DESC LIMIT 1;" 2>/dev/null || echo "none")

# ---- Build briefing ----
BRIEFING="[math-forge] Session briefing ($(date -u +%Y-%m-%dT%H:%M:%SZ))

QUEUE: ${IN_FLIGHT:-0} in-flight, ${SLOTS_OPEN} slots open"

if [[ -n "$COMPLETED_UNFETCHED" && "$COMPLETED_UNFETCHED" != "" ]]; then
    BRIEFING="${BRIEFING}
READY TO FETCH: ${COMPLETED_UNFETCHED}"
fi

if [[ -n "$RECENT_PROVEN" && "$RECENT_PROVEN" != "" ]]; then
    BRIEFING="${BRIEFING}
RECENT PROVEN: ${RECENT_PROVEN}"
fi

if [[ -n "$NEAR_MISS" && "$NEAR_MISS" != "" ]]; then
    BRIEFING="${BRIEFING}
TOP NEAR-MISS: ${NEAR_MISS}"
fi

BRIEFING="${BRIEFING}
KB: ${KB_COUNT} findings"

# Action items
ACTIONS=""
ACTION_NUM=1
if [[ -n "$COMPLETED_UNFETCHED" && "$COMPLETED_UNFETCHED" != "" ]]; then
    ACTIONS="${ACTIONS}
${ACTION_NUM}. Fetch ready results: ${COMPLETED_UNFETCHED}"
    ACTION_NUM=$((ACTION_NUM + 1))
fi
if [[ -n "$NEAR_MISS" && "$NEAR_MISS" != "" ]]; then
    ACTIONS="${ACTIONS}
${ACTION_NUM}. Close near-miss: ${NEAR_MISS}"
    ACTION_NUM=$((ACTION_NUM + 1))
fi
if [[ $SLOTS_OPEN -gt 0 ]]; then
    ACTIONS="${ACTIONS}
${ACTION_NUM}. ${SLOTS_OPEN} slots open for new submissions"
fi

if [[ -n "$ACTIONS" ]]; then
    BRIEFING="${BRIEFING}

ACTION ITEMS:${ACTIONS}"
fi

BRIEFING="${BRIEFING}

Use \`mk search <query>\` for KB queries. Use \`mk find <problem>\` for problem-level view."

# ---- Inject PATH via CLAUDE_ENV_FILE ----
if [[ -n "${CLAUDE_ENV_FILE:-}" ]]; then
    echo "export PATH=\"\$PATH:${PLUGIN_ROOT}/scripts\"" >> "$CLAUDE_ENV_FILE"
fi

# ---- Output as JSON with additionalContext ----
ESCAPED=$(printf '%s' "$BRIEFING" | python3 -c "import sys,json; print(json.dumps(sys.stdin.read()))" 2>/dev/null)

cat <<ENDJSON
{
  "hookSpecificOutput": {
    "hookEventName": "SessionStart",
    "additionalContext": ${ESCAPED}
  }
}
ENDJSON

exit 0
