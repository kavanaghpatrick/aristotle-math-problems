#!/usr/bin/env bash
# PostToolUse hook: Validate .lean file writes/edits
# Checks for: sorry replacement, false lemma references
set -uo pipefail

INPUT=$(cat)

# Extract fields from JSON
if command -v jq &>/dev/null; then
    FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty' 2>/dev/null)
    TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty' 2>/dev/null)
    OLD_STRING=$(echo "$INPUT" | jq -r '.tool_input.old_string // empty' 2>/dev/null)
    NEW_STRING=$(echo "$INPUT" | jq -r '.tool_input.new_string // empty' 2>/dev/null)
else
    FILE_PATH=$(echo "$INPUT" | grep -o '"file_path"[[:space:]]*:[[:space:]]*"[^"]*"' | head -1 | sed 's/.*"file_path"[[:space:]]*:[[:space:]]*"//;s/"$//')
    TOOL_NAME=$(echo "$INPUT" | grep -o '"tool_name"[[:space:]]*:[[:space:]]*"[^"]*"' | head -1 | sed 's/.*"tool_name"[[:space:]]*:[[:space:]]*"//;s/"$//')
    OLD_STRING=""
    NEW_STRING=""
fi

# Gap-targeting: validate .txt sketch files
if [[ "$FILE_PATH" == *.txt ]] && [[ "$FILE_PATH" == *sketch* || "$FILE_PATH" == *slot* ]]; then
    SKETCH_WARNINGS=()
    if grep -qiE '(Proof Strategy|Key Lemma|APPROACH [0-9]|Main Proof|Proof Assembly|Proof Outline|Proposed (Strategy|Approach|proof)|FALLBACK [0-9]|(PRIMARY|SECONDARY):|^###?\s+Lemma [0-9]|WHAT TO PROVE)' "$FILE_PATH" 2>/dev/null; then
        SKETCH_WARNINGS+=("[math-forge] WARNING: Sketch contains proof guidance. Gap-targeting: state only the bare conjecture.")
    fi
    LINE_COUNT=$(grep -cv '^\s*$' "$FILE_PATH" 2>/dev/null || echo 0)
    if [ "$LINE_COUNT" -gt 30 ]; then
        SKETCH_WARNINGS+=("[math-forge] WARNING: Sketch has ${LINE_COUNT} lines (max 30 for gap-targeting).")
    fi
    if [ ${#SKETCH_WARNINGS[@]} -gt 0 ]; then
        COMBINED=""
        for w in "${SKETCH_WARNINGS[@]}"; do
            COMBINED="${COMBINED:+$COMBINED | }${w}"
        done
        ESCAPED_REASON=$(printf '%s' "$COMBINED" | sed 's/"/\\"/g')
        echo "{\"hookSpecificOutput\": {\"hookEventName\": \"PostToolUse\", \"additionalContext\": \"${ESCAPED_REASON}\"}}"
    fi
    exit 0
fi

# Only act on .lean files
if [[ -z "$FILE_PATH" ]] || [[ "$FILE_PATH" != *.lean ]]; then
    exit 0
fi

if [[ ! -f "$FILE_PATH" ]]; then
    exit 0
fi

PLUGIN_ROOT="${CLAUDE_PLUGIN_ROOT:-$(dirname "$0")/../..}"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(cd "$PLUGIN_ROOT/.." && pwd)}"
TRACKING_DB="${PROJECT_DIR}/submissions/tracking.db"

WARNINGS=()
BLOCK=false
BLOCK_REASON=""

# ---- CHECK 1: Sorry replacement (HARD BLOCK) ----
if [[ "$TOOL_NAME" == "Edit" && -n "$OLD_STRING" && -n "$NEW_STRING" ]]; then
    OLD_HAS_SORRY=$(echo "$OLD_STRING" | grep -c '\bsorry\b' 2>/dev/null || true)
    NEW_HAS_SORRY=$(echo "$NEW_STRING" | grep -c '\bsorry\b' 2>/dev/null || true)
    OLD_HAS_SORRY=${OLD_HAS_SORRY:-0}
    NEW_HAS_SORRY=${NEW_HAS_SORRY:-0}

    if [[ "$OLD_HAS_SORRY" -eq 0 && "$NEW_HAS_SORRY" -gt 0 ]]; then
        OLD_HAS_PROOF=$(echo "$OLD_STRING" | grep -cE '(by|:=|exact|apply|simp|omega|decide|rfl|calc|have|let|show|intro|cases|induction)' 2>/dev/null || true)
        OLD_HAS_PROOF=${OLD_HAS_PROOF:-0}
        if [[ "$OLD_HAS_PROOF" -gt 0 ]]; then
            BLOCK=true
            BLOCK_REASON="[math-forge] BLOCKED: Edit replaces existing proof code with sorry. This violates project rule: 'NEVER replace existing proof code with sorry'. Restore the proof or fix it without introducing sorry."
        fi
    fi
fi

# ---- CHECK 2: False lemma references (ADVISORY WARNING) ----
if [[ -f "$TRACKING_DB" ]]; then
    FALSE_LEMMAS=$(sqlite3 "$TRACKING_DB" "SELECT lemma_name FROM false_lemmas;" 2>/dev/null)
    if [[ -n "$FALSE_LEMMAS" ]]; then
        while IFS= read -r lemma; do
            if [[ -n "$lemma" ]] && grep -q "$lemma" "$FILE_PATH" 2>/dev/null; then
                WARNINGS+=("[math-forge] WARNING: File references false lemma '${lemma}' (disproven). Check \`mk failed ${lemma}\` for details.")
            fi
        done <<< "$FALSE_LEMMAS"
    fi
fi

# ---- OUTPUT ----
if [[ "$BLOCK" == true ]]; then
    echo "{\"decision\": \"block\", \"reason\": \"${BLOCK_REASON}\"}"
    exit 0
fi

if [[ ${#WARNINGS[@]} -gt 0 ]]; then
    COMBINED=""
    for w in "${WARNINGS[@]}"; do
        if [[ -n "$COMBINED" ]]; then
            COMBINED="${COMBINED} | ${w}"
        else
            COMBINED="${w}"
        fi
    done
    ESCAPED_REASON=$(printf '%s' "$COMBINED" | sed 's/"/\\"/g')
    echo "{\"hookSpecificOutput\": {\"hookEventName\": \"PostToolUse\", \"additionalContext\": \"${ESCAPED_REASON}\"}}"
fi

exit 0
