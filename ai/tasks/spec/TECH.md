# Technical Architecture: math-forge

## Research Findings

### SQLite FTS5 External Content Tables

FTS5 external content tables maintain a separate virtual table backed by a canonical data table. The critical implementation detail: the user must ensure consistency between the content table and the FTS index via triggers. Three triggers are required (INSERT, DELETE, UPDATE). The DELETE trigger uses the special syntax `INSERT INTO fts_table(fts_table, rowid, col1, col2) VALUES('delete', old.id, old.col1, old.col2)` to remove old tokens. UPDATE triggers must delete the old entry first, then insert the new one. If the external content row is modified before the FTS delete trigger fires, the wrong tokens may be removed, causing index corruption.

For math-forge, the `porter` tokenizer handles English stemming well but mathematical notation (LaTeX, theorem names like `erdos_850_triple_factors`) tokenizes poorly. Mitigation: supplement FTS5 MATCH queries with exact-match SQL on structured fields (`problem_id`, `domain`, `technique`).

Sources: [SQLite FTS5 Extension](https://www.sqlite.org/fts5.html), [FTS5 in Practice](https://thelinuxcode.com/sqlite-full-text-search-fts5-in-practice-fast-search-ranking-and-real-world-patterns/), [Optimizing FTS5 External Content Tables](https://sqlite.work/optimizing-fts5-external-content-tables-and-vacuum-interactions/)

### Claude Code Plugin Hooks System

The hooks system supports 14 event types. Key events for math-forge:

- **SessionStart**: stdout is added as context Claude can see. JSON with `additionalContext` field is supported. `CLAUDE_ENV_FILE` available for persisting environment variables. Matchers: `startup`, `resume`, `clear`, `compact`.
- **PostToolUse**: fires after successful tool completion. Receives `tool_input` and `tool_response` on stdin. Decision control: `decision: "block"` with `reason` prevents the action (advisory since tool already ran). Matcher on tool name (regex): `Edit|Write`.
- **SubagentStart**: can inject `additionalContext` into subagent context. Matcher on agent type.

Plugin hooks are defined in `hooks/hooks.json` with a `description` field at top level. The `${CLAUDE_PLUGIN_ROOT}` variable resolves to the plugin directory. Hooks from plugins are read-only in the `/hooks` menu. Exit code 0 = success (JSON parsed from stdout), exit code 2 = blocking error (stderr fed to Claude), other exit codes = non-blocking error.

Sources: [Claude Code Hooks Reference](https://code.claude.com/docs/en/hooks), [Claude Code Hooks Guide](https://claude.com/blog/how-to-configure-hooks), [Plugin Hooks Reference](https://github.com/anthropics/claude-code/blob/main/plugins/plugin-dev/skills/hook-development/SKILL.md)

### Bash CLI + SQLite3 Wrapper Patterns

The gpu-forge `kb` script demonstrates the production pattern: 3-level DB path resolution (`env var > CLAUDE_PLUGIN_ROOT > script-relative`), `escape_sql()` function for SQL injection prevention, `run_sql()` wrapper with error checking and friendly constraint violation messages, and `case` statement dispatch for subcommands. Key design choices: `-header -column` for formatted output, `sqlite3` CLI for zero-dependency execution, `BM25` weighting parameters for search relevance tuning.

Sources: [SQLite CLI](https://sqlite.org/cli.html), gpu-forge reference implementation at `/tmp/gpu-forge/scripts/kb`

---

## System Architecture

```
                     Claude Code Session
                            |
                +-----------+-----------+
                |                       |
         SessionStart Hook         PostToolUse Hook
         (context-loader.sh)       (lean-validator.sh)
                |                       |
                v                       v
         +-------------+        +--------------+
         | tracking.db  |        | .lean file   |
         | knowledge.db |        | diff/content |
         +-------------+        +--------------+
                |
                v
         [~300 token briefing]
         injected as additionalContext

                     +-------+
                     |  mk   |  <-- Bash CLI tool
                     +-------+
                     |
          +----------+----------+
          |          |          |
       search      find     stats   ...
          |          |          |
          v          v          v
     knowledge.db (FTS5 + structured queries)
                     |
         +-----------+-----------+
         |                       |
    findings table          strategies table
    (FTS5 indexed)         (structured queries)

         extract_findings.py
              |
    .lean result files --> parsed --> findings inserted
```

### Data Flow

1. **Session start**: `context-loader.sh` queries both `tracking.db` (queue status, in-flight submissions) and `knowledge.db` (KB stats, recent findings). Outputs ~300 token briefing as `additionalContext`.

2. **Sketch writing**: Claude invokes `mk search` and `mk find` via Bash tool to query knowledge.db for relevant prior findings, failed approaches, and proven techniques.

3. **Result processing**: After `/fetch` downloads a result, `extract_findings.py` parses the `.lean` file and inserts structured findings into knowledge.db.

4. **Lean validation**: `lean-validator.sh` fires on `Write|Edit` of `.lean` files, checking for sorry replacement and false lemma references.

5. **Subagent context**: SubagentStart hook injects relevant KB findings into debate/research subagents (future iteration).

---

## Database Schema

### knowledge.db (Complete SQL)

```sql
-- Math-Forge Knowledge Database Schema
-- Separate from tracking.db: derived, reconstructible, independent evolution

PRAGMA journal_mode=WAL;
PRAGMA foreign_keys=ON;

-- ============================================================
-- DOMAINS: Mathematical classification taxonomy
-- ============================================================
CREATE TABLE IF NOT EXISTS domains (
    id TEXT PRIMARY KEY,           -- 'nt', 'algebra', 'combinatorics', 'analysis'
    name TEXT NOT NULL,            -- 'Number Theory', 'Algebra', etc.
    description TEXT
);

INSERT OR IGNORE INTO domains (id, name, description) VALUES
('nt',             'Number Theory',   'Primes, divisibility, modular arithmetic, Diophantine'),
('algebra',        'Algebra',         'Groups, rings, fields, representation theory'),
('combinatorics',  'Combinatorics',   'Graphs, hypergraphs, extremal, Ramsey'),
('analysis',       'Analysis',        'Real/complex analysis, measure theory, functional');

-- ============================================================
-- FINDINGS: Core knowledge atoms — every discrete piece of knowledge
-- ============================================================
CREATE TABLE IF NOT EXISTS findings (
    id INTEGER PRIMARY KEY AUTOINCREMENT,

    -- Classification
    finding_type TEXT NOT NULL CHECK(finding_type IN (
        'theorem',           -- A proven mathematical result
        'technique',         -- A proof technique that worked
        'failure',           -- An approach that failed and why
        'false_lemma',       -- A disproven claim with counterexample
        'computation',       -- A computational result (witness, pattern, bound)
        'mathlib_api',       -- A useful Mathlib API discovery
        'insight'            -- A strategic/structural observation
    )),
    domain_id TEXT REFERENCES domains(id),

    -- Content
    title TEXT NOT NULL,              -- Short descriptive title
    description TEXT NOT NULL,        -- Full finding text
    problem_id TEXT,                  -- e.g., 'erdos_364', 'ft_p3', 'kurepa'

    -- Provenance
    source_slot INTEGER,              -- Slot number from submission system
    source_submission_uuid TEXT,      -- UUID from tracking.db
    source_file TEXT,                 -- Path to .lean or .txt file

    -- Proof details (for theorem/technique findings)
    theorem_name TEXT,                -- Lean theorem name if applicable
    theorem_statement TEXT,           -- Lean or English statement
    proof_technique TEXT,             -- Primary technique used
    mathlib_imports TEXT,             -- Comma-separated key Mathlib imports
    proof_lines INTEGER,             -- Lines of proof code

    -- Failure details (for failure/false_lemma findings)
    counterexample TEXT,             -- Specific counterexample if applicable
    why_failed TEXT,                 -- Explanation of failure
    avoid_pattern TEXT,              -- What NOT to repeat

    -- Quality
    confidence TEXT CHECK(confidence IN (
        'verified',          -- Lean-verified or Aristotle-proven
        'high',              -- Strong evidence, multiple confirmations
        'medium',            -- Single source, plausible
        'low',               -- Speculative, needs validation
        'disproven'          -- Known false
    )) DEFAULT 'medium',

    -- Metadata
    created_at TEXT DEFAULT (datetime('now')),
    updated_at TEXT DEFAULT (datetime('now')),
    tags TEXT,                       -- Comma-separated free-form tags
    notes TEXT                       -- Additional context
);

-- ============================================================
-- STRATEGIES: Problem-level approach tracking
-- ============================================================
CREATE TABLE IF NOT EXISTS strategies (
    id INTEGER PRIMARY KEY AUTOINCREMENT,

    -- Problem identification
    problem_id TEXT NOT NULL,         -- e.g., 'erdos_364', 'ft_p3_q71mod72'
    problem_name TEXT NOT NULL,       -- Human-readable name
    domain_id TEXT REFERENCES domains(id),

    -- Strategy details
    approach_name TEXT NOT NULL,      -- e.g., 'QR + Euler criterion', 'pigeonhole'
    approach_description TEXT,        -- How the approach works

    -- Outcome
    outcome TEXT NOT NULL CHECK(outcome IN (
        'proven',            -- Approach succeeded, result proven
        'partial',           -- Some progress, not complete
        'failed',            -- Approach tried and failed
        'in_flight',         -- Currently being tried (submitted)
        'untried'            -- Proposed but not yet attempted
    )),

    -- Linkage
    submission_slot INTEGER,          -- Which slot attempted this
    submission_uuid TEXT,
    finding_ids TEXT,                 -- Comma-separated finding IDs from this attempt

    -- Metadata
    attempts INTEGER DEFAULT 1,
    last_attempted TEXT DEFAULT (datetime('now')),
    learned TEXT,                     -- What we learned from this attempt
    created_at TEXT DEFAULT (datetime('now')),

    -- Prevent duplicate strategy tracking
    UNIQUE(problem_id, approach_name)
);

-- ============================================================
-- PROBLEMS: Problem-level summary (aggregation layer)
-- ============================================================
CREATE TABLE IF NOT EXISTS problems (
    id TEXT PRIMARY KEY,              -- e.g., 'erdos_364', 'ft_p3'
    name TEXT NOT NULL,               -- Human-readable name
    domain_id TEXT REFERENCES domains(id),

    -- Status
    status TEXT CHECK(status IN (
        'open',              -- Still unsolved
        'proven',            -- Fully proven
        'partial',           -- Some cases/bounds proven
        'false',             -- Disproven / counterexample found
        'in_flight'          -- Active attempts underway
    )) DEFAULT 'open',

    -- Counts (denormalized for fast queries)
    submission_count INTEGER DEFAULT 0,
    proven_count INTEGER DEFAULT 0,
    failed_count INTEGER DEFAULT 0,

    -- Content
    statement TEXT,                   -- Mathematical statement
    best_result TEXT,                 -- Best result so far

    created_at TEXT DEFAULT (datetime('now')),
    updated_at TEXT DEFAULT (datetime('now'))
);

-- ============================================================
-- CACHE: Aristotle queue status cache
-- ============================================================
CREATE TABLE IF NOT EXISTS queue_cache (
    id INTEGER PRIMARY KEY CHECK(id = 1),   -- Singleton row
    cached_at TEXT NOT NULL,
    in_flight INTEGER DEFAULT 0,
    slots_open INTEGER DEFAULT 5,
    ready_to_fetch TEXT,              -- JSON array of slot numbers
    recently_completed TEXT,          -- JSON array of {slot, status, sorry_count}
    top_near_miss TEXT,               -- JSON: {slot, problem, sorry_count, sorry_location}
    raw_json TEXT                     -- Full API response for debugging
);

-- ============================================================
-- FTS5: Full-text search over findings
-- ============================================================
CREATE VIRTUAL TABLE IF NOT EXISTS findings_fts USING fts5(
    title,
    description,
    problem_id UNINDEXED,
    theorem_name,
    theorem_statement,
    proof_technique,
    tags,
    why_failed,
    content=findings,
    content_rowid=id,
    tokenize='porter unicode61'
);

-- ============================================================
-- FTS5 SYNC TRIGGERS: Keep FTS index in sync with findings table
-- ============================================================
CREATE TRIGGER IF NOT EXISTS findings_fts_insert AFTER INSERT ON findings BEGIN
    INSERT INTO findings_fts(rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES (new.id, new.title, new.description, new.theorem_name, new.theorem_statement, new.proof_technique, new.tags, new.why_failed);
END;

CREATE TRIGGER IF NOT EXISTS findings_fts_delete AFTER DELETE ON findings BEGIN
    INSERT INTO findings_fts(findings_fts, rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES ('delete', old.id, old.title, old.description, old.theorem_name, old.theorem_statement, old.proof_technique, old.tags, old.why_failed);
END;

CREATE TRIGGER IF NOT EXISTS findings_fts_update AFTER UPDATE ON findings BEGIN
    INSERT INTO findings_fts(findings_fts, rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES ('delete', old.id, old.title, old.description, old.theorem_name, old.theorem_statement, old.proof_technique, old.tags, old.why_failed);
    INSERT INTO findings_fts(rowid, title, description, theorem_name, theorem_statement, proof_technique, tags, why_failed)
    VALUES (new.id, new.title, new.description, new.theorem_name, new.theorem_statement, new.proof_technique, new.tags, new.why_failed);
END;

-- ============================================================
-- INDEXES: Performance optimization
-- ============================================================
CREATE INDEX IF NOT EXISTS idx_findings_type ON findings(finding_type);
CREATE INDEX IF NOT EXISTS idx_findings_domain ON findings(domain_id);
CREATE INDEX IF NOT EXISTS idx_findings_problem ON findings(problem_id);
CREATE INDEX IF NOT EXISTS idx_findings_slot ON findings(source_slot);
CREATE INDEX IF NOT EXISTS idx_findings_confidence ON findings(confidence);
CREATE INDEX IF NOT EXISTS idx_findings_created ON findings(created_at);

CREATE INDEX IF NOT EXISTS idx_strategies_problem ON strategies(problem_id);
CREATE INDEX IF NOT EXISTS idx_strategies_outcome ON strategies(outcome);
CREATE INDEX IF NOT EXISTS idx_strategies_domain ON strategies(domain_id);

CREATE INDEX IF NOT EXISTS idx_problems_domain ON problems(domain_id);
CREATE INDEX IF NOT EXISTS idx_problems_status ON problems(status);

-- ============================================================
-- VIEWS: Common query patterns
-- ============================================================

-- All proven techniques grouped by frequency
CREATE VIEW IF NOT EXISTS v_proven_techniques AS
SELECT
    proof_technique,
    domain_id,
    COUNT(*) as usage_count,
    GROUP_CONCAT(source_slot, ', ') as slots
FROM findings
WHERE finding_type = 'theorem' AND confidence = 'verified' AND proof_technique IS NOT NULL
GROUP BY proof_technique, domain_id
ORDER BY usage_count DESC;

-- Failed approaches with attempt counts
CREATE VIEW IF NOT EXISTS v_failed_approaches AS
SELECT
    problem_id,
    title,
    why_failed,
    avoid_pattern,
    source_slot,
    created_at
FROM findings
WHERE finding_type IN ('failure', 'false_lemma')
ORDER BY created_at DESC;

-- Problem dashboard: everything about each problem
CREATE VIEW IF NOT EXISTS v_problem_dashboard AS
SELECT
    p.id,
    p.name,
    p.domain_id,
    p.status,
    p.submission_count,
    p.proven_count,
    p.failed_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'theorem') as theorem_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'failure') as failure_count,
    (SELECT COUNT(*) FROM findings f WHERE f.problem_id = p.id AND f.finding_type = 'false_lemma') as false_lemma_count,
    (SELECT COUNT(*) FROM strategies s WHERE s.problem_id = p.id AND s.outcome = 'in_flight') as in_flight_count,
    (SELECT COUNT(*) FROM strategies s WHERE s.problem_id = p.id AND s.outcome = 'untried') as untried_count
FROM problems p;

-- Near-miss findings (1-sorry results worth closing)
CREATE VIEW IF NOT EXISTS v_near_miss_findings AS
SELECT
    f.id, f.title, f.problem_id, f.source_slot, f.notes
FROM findings f
WHERE f.finding_type = 'theorem'
  AND f.confidence = 'medium'
  AND f.notes LIKE '%sorry=1%'
ORDER BY f.created_at DESC;
```

---

## Plugin Structure

```
math-forge/
├── .claude-plugin/
│   └── plugin.json                    # Plugin manifest
├── data/
│   ├── schema.sql                     # Complete knowledge.db schema (above)
│   └── knowledge.db                   # Created at bootstrap (gitignored)
├── hooks/
│   ├── hooks.json                     # Hook event configuration
│   └── scripts/
│       ├── context-loader.sh          # SessionStart: briefing injection
│       ├── lean-validator.sh          # PostToolUse: .lean file validation
│       └── subagent-context.sh        # SubagentStart: KB context injection (v2)
├── scripts/
│   ├── mk                            # KB CLI tool (bash)
│   ├── extract_findings.py           # Result extraction pipeline (python3)
│   └── migrate_tracking.py           # One-time bootstrap migration (python3)
├── agents/
│   └── investigate.md                 # Investigation agent (v2)
└── tests/
    ├── test_mk.bats                   # BATS tests for mk CLI
    ├── test_hooks.bats                # BATS tests for hooks
    └── test_extract.bats              # BATS tests for extraction
```

### plugin.json

```json
{
  "name": "math-forge",
  "version": "0.1.0",
  "description": "Mathematical knowledge infrastructure for proof pipeline — FTS5 search across 500+ findings, session briefings, result extraction, and Lean validation",
  "author": "Patrick Kavanagh",
  "keywords": [
    "mathematics",
    "theorem-proving",
    "knowledge-base",
    "lean4",
    "aristotle",
    "proof-strategy"
  ]
}
```

---

## Hook Implementations

### hooks/hooks.json

```json
{
  "description": "Math-forge lifecycle hooks: session briefing, Lean file validation, subagent context",
  "hooks": {
    "SessionStart": [
      {
        "matcher": "startup|resume",
        "hooks": [
          {
            "type": "command",
            "command": "bash ${CLAUDE_PLUGIN_ROOT}/hooks/scripts/context-loader.sh",
            "timeout": 5,
            "statusMessage": "Loading math-forge knowledge context..."
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "Write|Edit",
        "hooks": [
          {
            "type": "command",
            "command": "bash ${CLAUDE_PLUGIN_ROOT}/hooks/scripts/lean-validator.sh",
            "timeout": 3
          }
        ]
      }
    ]
  }
}
```

### hooks/scripts/context-loader.sh

```bash
#!/usr/bin/env bash
# SessionStart hook: Generate ~300 token briefing from tracking.db + knowledge.db
# Outputs JSON with additionalContext for Claude's system prompt
set -uo pipefail

# Resolve paths
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

# Recent proven results (last 7 days)
RECENT_PROVEN=$(q "$TRACKING_DB" \
    "SELECT GROUP_CONCAT(filename || ' (' || proven_count || ' theorems)', ', ')
     FROM submissions
     WHERE verified = 1 AND sorry_count = 0
     AND completed_at > datetime('now', '-7 days')
     ORDER BY completed_at DESC LIMIT 3;")

# Top near-miss (1 sorry, highest proven count)
NEAR_MISS=$(q "$TRACKING_DB" \
    "SELECT filename || ' (' || sorry_count || ' sorry, ' || proven_count || ' proven)'
     FROM submissions
     WHERE status = 'completed' AND sorry_count = 1 AND proven_count > 5
     AND id NOT IN (SELECT submission_id FROM submission_false_lemma_targets)
     ORDER BY proven_count DESC LIMIT 1;")

# ---- Gather data from knowledge.db ----
KB_COUNT=$(q "$KNOWLEDGE_DB" "SELECT COUNT(*) FROM findings;" 2>/dev/null || echo "0")
KB_RECENT=$(q "$KNOWLEDGE_DB" \
    "SELECT title FROM findings ORDER BY created_at DESC LIMIT 1;" 2>/dev/null || echo "none")

# ---- Check staleness ----
LAST_SUBMIT=$(q "$TRACKING_DB" \
    "SELECT submitted_at FROM submissions WHERE submitted_at IS NOT NULL ORDER BY submitted_at DESC LIMIT 1;")
STALENESS_NOTE=""
if [[ -n "$LAST_SUBMIT" ]]; then
    # Calculate hours since last submission (approximate)
    LAST_EPOCH=$(date -j -f "%Y-%m-%d %H:%M:%S" "${LAST_SUBMIT}" "+%s" 2>/dev/null || echo "0")
    NOW_EPOCH=$(date "+%s")
    if [[ "$LAST_EPOCH" -gt 0 ]]; then
        HOURS_AGO=$(( (NOW_EPOCH - LAST_EPOCH) / 3600 ))
        if [[ $HOURS_AGO -gt 6 ]]; then
            STALENESS_NOTE="NOTE: Last DB update was ${HOURS_AGO}h ago. Run /project:status to refresh."
        fi
    fi
fi

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

if [[ -n "$STALENESS_NOTE" ]]; then
    BRIEFING="${BRIEFING}

${STALENESS_NOTE}"
fi

BRIEFING="${BRIEFING}

Use \`mk search <query>\` for KB queries. Use \`mk find <problem>\` for problem-level view."

# ---- Output as JSON with additionalContext ----
# Escape for JSON: replace newlines, quotes, backslashes
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
```

### hooks/scripts/lean-validator.sh

```bash
#!/usr/bin/env bash
# PostToolUse hook: Validate .lean file writes/edits
# Checks for: sorry replacement, false lemma references
# Input: JSON on stdin with tool_input and tool_response
set -uo pipefail

# Read JSON from stdin
INPUT=$(cat)

# Extract file_path from tool_input
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

# Only act on .lean files
if [[ -z "$FILE_PATH" ]] || [[ "$FILE_PATH" != *.lean ]]; then
    exit 0
fi

# Check if file exists
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
# Only for Edit tool: check if old_string had proof content and new_string has sorry
if [[ "$TOOL_NAME" == "Edit" && -n "$OLD_STRING" && -n "$NEW_STRING" ]]; then
    OLD_HAS_SORRY=$(echo "$OLD_STRING" | grep -c '\bsorry\b' 2>/dev/null || echo "0")
    NEW_HAS_SORRY=$(echo "$NEW_STRING" | grep -c '\bsorry\b' 2>/dev/null || echo "0")

    if [[ "$OLD_HAS_SORRY" -eq 0 && "$NEW_HAS_SORRY" -gt 0 ]]; then
        # old_string had no sorry, new_string introduces sorry
        # Check if old_string had actual proof content (not just a declaration)
        OLD_HAS_PROOF=$(echo "$OLD_STRING" | grep -cE '(by|:=|exact|apply|simp|omega|decide|rfl|calc|have|let|show|intro|cases|induction)' 2>/dev/null || echo "0")
        if [[ "$OLD_HAS_PROOF" -gt 0 ]]; then
            BLOCK=true
            BLOCK_REASON="[math-forge] BLOCKED: Edit replaces existing proof code with sorry. This violates project rule: 'NEVER replace existing proof code with sorry'. Restore the proof or fix it without introducing sorry."
        fi
    fi
fi

# ---- CHECK 2: False lemma references (ADVISORY WARNING) ----
if [[ -f "$TRACKING_DB" ]]; then
    # Get list of false lemma names
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
    # Combine warnings into reason string
    COMBINED=""
    for w in "${WARNINGS[@]}"; do
        if [[ -n "$COMBINED" ]]; then
            COMBINED="${COMBINED} | ${w}"
        else
            COMBINED="${w}"
        fi
    done
    # Advisory: allow but warn
    ESCAPED_REASON=$(printf '%s' "$COMBINED" | sed 's/"/\\"/g')
    echo "{\"hookSpecificOutput\": {\"hookEventName\": \"PostToolUse\", \"additionalContext\": \"${ESCAPED_REASON}\"}}"
fi

exit 0
```

---

## KB CLI Tool (`mk`)

### Architecture

`mk` is a bash script (~350 lines) that dispatches subcommands to sqlite3 queries against knowledge.db. It follows the gpu-forge `kb` pattern: 3-level DB resolution, `escape_sql()` for injection prevention, `run_sql()` wrapper with error handling, and `case` statement routing.

### Command Routing

```bash
#!/usr/bin/env bash
# mk — Math-forge Knowledge Base CLI
# Usage: mk <command> [args...]

set -uo pipefail

# 3-level DB path resolution
if [ -n "${MATH_FORGE_DB:-}" ]; then
    DB="$MATH_FORGE_DB"
elif [ -n "${CLAUDE_PLUGIN_ROOT:-}" ]; then
    DB="${CLAUDE_PLUGIN_ROOT}/data/knowledge.db"
else
    DB="$(dirname "$0")/../data/knowledge.db"
fi

# Also need tracking.db for cross-queries
if [ -n "${CLAUDE_PROJECT_DIR:-}" ]; then
    TRACKING_DB="${CLAUDE_PROJECT_DIR}/submissions/tracking.db"
else
    TRACKING_DB="$(dirname "$0")/../../submissions/tracking.db"
fi

# Color support (TTY-aware)
if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
    GREEN='\033[0;32m'; RED='\033[0;31m'; YELLOW='\033[0;33m'
    CYAN='\033[0;36m'; BOLD='\033[1m'; RESET='\033[0m'
else
    GREEN=''; RED=''; YELLOW=''; CYAN=''; BOLD=''; RESET=''
fi

escape_sql() {
    printf '%s' "$1" | sed "s/'/''/g"
}

run_sql() {
    local db="$1"; shift
    local output
    output=$(sqlite3 "$db" "$@" 2>&1)
    local rc=$?
    if [ $rc -ne 0 ]; then
        echo "[math-forge] ERROR: sqlite3 failed: $output" >&2
        return $rc
    fi
    [ -n "$output" ] && printf '%s\n' "$output"
    return 0
}

# Normalize problem ID: strip spaces, underscores, lowercase
normalize_problem() {
    echo "$1" | tr '[:upper:]' '[:lower:]' | sed 's/[ _-]//g'
}

case "${1:-help}" in
    search)    # ... FTS5 search
    ;;
    find)      # ... problem-level lookup
    ;;
    strategies) # ... proven strategies by domain
    ;;
    failed)    # ... failed approaches
    ;;
    stats)     # ... dashboard
    ;;
    init)      # ... initialize DB from schema
    ;;
    help|*)    # ... usage
    ;;
esac
```

### Core Queries

**`mk search <query>`** — FTS5 full-text search with BM25 ranking:

```sql
-- Layer 1 (default: 5 results)
SELECT f.id,
       CASE f.finding_type
           WHEN 'theorem' THEN '[PROVEN]'
           WHEN 'technique' THEN '[TECHNIQUE]'
           WHEN 'failure' THEN '[FAILED]'
           WHEN 'false_lemma' THEN '[FALSE]'
           WHEN 'computation' THEN '[COMPUTED]'
           WHEN 'insight' THEN '[INSIGHT]'
           ELSE '[' || UPPER(f.finding_type) || ']'
       END as badge,
       f.title,
       COALESCE('Technique: ' || f.proof_technique, SUBSTR(f.description, 1, 120)),
       'Domain: ' || COALESCE(f.domain_id, '?') || ' | Slot: ' || COALESCE(f.source_slot, '?'),
       rank
FROM findings_fts fts
JOIN findings f ON f.id = fts.rowid
WHERE findings_fts MATCH '{title description theorem_statement proof_technique tags why_failed}:' || ?
ORDER BY bm25(findings_fts, 10.0, 5.0, 1.0, 5.0, 3.0, 2.0, 3.0)
LIMIT ?;
```

BM25 weights: `title=10, description=5, theorem_name=1 (UNINDEXED so ignored), theorem_statement=5, proof_technique=3, tags=2, why_failed=3`. Title and statement matches rank highest.

**`mk find <problem-id>`** — Problem-level aggregation:

```sql
-- 1. Problem summary
SELECT * FROM problems WHERE id LIKE '%' || ? || '%';

-- 2. All findings for this problem
SELECT finding_type, title, COALESCE(source_slot, ''), confidence
FROM findings WHERE problem_id LIKE '%' || ? || '%'
ORDER BY finding_type, created_at DESC;

-- 3. All strategies for this problem
SELECT approach_name, outcome, attempts, submission_slot, learned
FROM strategies WHERE problem_id LIKE '%' || ? || '%'
ORDER BY outcome, last_attempted DESC;

-- 4. Related false lemmas from tracking.db (cross-DB query)
SELECT lemma_name, why_false, counterexample
FROM false_lemmas WHERE lemma_name LIKE '%' || ? || '%'
                     OR impact LIKE '%' || ? || '%';

-- 5. Submissions from tracking.db
SELECT filename, status, sorry_count, proven_count, completed_at
FROM submissions WHERE problem_id LIKE '%' || ? || '%'
                    OR filename LIKE '%' || ? || '%'
ORDER BY created_at DESC LIMIT 10;
```

**`mk strategies [domain]`** — Proven techniques by frequency:

```sql
SELECT proof_technique, COUNT(*) as cnt,
       GROUP_CONCAT(DISTINCT source_slot) as slots,
       domain_id
FROM findings
WHERE finding_type = 'theorem' AND confidence = 'verified'
  AND proof_technique IS NOT NULL
  AND (domain_id = ? OR ? IS NULL)
GROUP BY proof_technique, domain_id
ORDER BY cnt DESC;
```

**`mk failed [keyword]`** — Failed approaches and false lemmas:

```sql
-- From knowledge.db
SELECT title, why_failed, avoid_pattern, source_slot, problem_id
FROM findings
WHERE finding_type IN ('failure', 'false_lemma')
  AND (title LIKE '%' || ? || '%' OR why_failed LIKE '%' || ? || '%' OR problem_id LIKE '%' || ? || '%')
ORDER BY created_at DESC;

-- Cross-check tracking.db
SELECT lemma_name, why_false, avoid_pattern, evidence_level
FROM false_lemmas
WHERE lemma_name LIKE '%' || ? || '%' OR why_false LIKE '%' || ? || '%';
```

**`mk stats`** — Dashboard:

```sql
-- Finding counts by type
SELECT finding_type, COUNT(*) FROM findings GROUP BY finding_type;

-- Domain distribution
SELECT domain_id, COUNT(*) FROM findings GROUP BY domain_id;

-- Freshness
SELECT MAX(created_at) FROM findings;

-- Strategy outcomes
SELECT outcome, COUNT(*) FROM strategies GROUP BY outcome;
```

### Output Formatting

All output follows the UX spec: 2-space indentation, `[STATUS]` badges, horizontal rules with `---`, relative timestamps for Layer 1, ISO for Layer 2 (`--verbose`). Color gated on `[ -t 1 ] && [ -z "${NO_COLOR:-}" ]`.

---

## Result Extraction Pipeline

### scripts/extract_findings.py

Python3 script that parses Aristotle result files and inserts structured findings into knowledge.db.

```python
#!/usr/bin/env python3
"""extract_findings.py — Parse Aristotle .lean result files into knowledge.db findings.

Usage:
    python3 extract_findings.py <result_file> [--slot N] [--problem-id ID] [--db PATH]

Extraction stages:
    1. Structural: theorem names, lemma names, def names (regex)
    2. Import analysis: Mathlib imports used (regex)
    3. Metric: sorry count, axiom count, proof line count
    4. Technique inference: heuristic from tactics used (regex)
    5. Finding generation: one finding per theorem proved
"""

import re
import sys
import sqlite3
import argparse
from pathlib import Path
from datetime import datetime

# --- Regex patterns for Lean 4 extraction ---

# Theorem/lemma/def declarations
DECL_RE = re.compile(
    r'^(theorem|lemma|def|noncomputable def|instance)\s+'
    r'(\w+)',
    re.MULTILINE
)

# Mathlib imports
IMPORT_RE = re.compile(r'^import\s+(Mathlib\.\w[\w.]*)', re.MULTILINE)

# Sorry locations
SORRY_RE = re.compile(r'\bsorry\b')

# Axiom declarations
AXIOM_RE = re.compile(r'^axiom\s+(\w+)', re.MULTILINE)

# Tactic usage (for technique inference)
TACTIC_PATTERNS = {
    'native_decide': re.compile(r'\bnative_decide\b'),
    'decide': re.compile(r'\bdecide\b'),
    'omega': re.compile(r'\bomega\b'),
    'simp': re.compile(r'\bsimp\b'),
    'ring': re.compile(r'\bring\b'),
    'norm_num': re.compile(r'\bnorm_num\b'),
    'induction': re.compile(r'\binduction\b'),
    'cases': re.compile(r'\bcases\b'),
    'contradiction': re.compile(r'\bcontradiction\b'),
    'exact': re.compile(r'\bexact\b'),
    'apply': re.compile(r'\bapply\b'),
    'calc': re.compile(r'\bcalc\b'),
    'interval_cases': re.compile(r'\binterval_cases\b'),
    'field_simp': re.compile(r'\bfield_simp\b'),
    'zify': re.compile(r'\bzify\b'),
    'push_cast': re.compile(r'\bpush_cast\b'),
}

# Technique inference heuristics
TECHNIQUE_MAP = {
    'native_decide': 'finite computation (native_decide)',
    'decide': 'finite computation (decide)',
    'omega': 'linear arithmetic (omega)',
    'norm_num': 'numerical normalization',
    'ring': 'ring tactic',
    'induction': 'induction',
    'interval_cases': 'interval case analysis',
    'field_simp': 'field simplification',
    'calc': 'calculational proof',
}


def extract_from_lean(content: str, filepath: str) -> dict:
    """Extract structured data from a .lean file."""

    # Declarations
    declarations = []
    for match in DECL_RE.finditer(content):
        decl_type = match.group(1)
        decl_name = match.group(2)
        # Find the statement (text until := or where or by)
        start = match.end()
        stmt_match = re.search(r'(:=|\bwhere\b|\bby\b)', content[start:start+500])
        statement = content[match.start():start + (stmt_match.start() if stmt_match else 200)].strip()

        # Check if this specific declaration has sorry
        # Look for 'sorry' between this declaration and the next one
        next_decl = DECL_RE.search(content, start)
        end_pos = next_decl.start() if next_decl else len(content)
        block = content[start:end_pos]
        has_sorry = bool(SORRY_RE.search(block))

        declarations.append({
            'type': decl_type,
            'name': decl_name,
            'statement': statement[:500],  # Truncate long statements
            'has_sorry': has_sorry,
            'line_count': block.count('\n'),
        })

    # Imports
    imports = [m.group(1) for m in IMPORT_RE.finditer(content)]

    # Global metrics
    sorry_count = len(SORRY_RE.findall(content))
    axiom_matches = AXIOM_RE.findall(content)
    total_lines = content.count('\n') + 1

    # Technique inference
    tactic_counts = {}
    for name, pattern in TACTIC_PATTERNS.items():
        count = len(pattern.findall(content))
        if count > 0:
            tactic_counts[name] = count

    # Determine primary technique
    primary_technique = None
    if tactic_counts:
        # Priority: specific tactics first
        for tactic in ['native_decide', 'decide', 'induction', 'calc', 'interval_cases']:
            if tactic in tactic_counts:
                primary_technique = TECHNIQUE_MAP.get(tactic, tactic)
                break
        if not primary_technique:
            # Most-used tactic
            top_tactic = max(tactic_counts, key=tactic_counts.get)
            primary_technique = TECHNIQUE_MAP.get(top_tactic, top_tactic)

    return {
        'declarations': declarations,
        'imports': imports,
        'sorry_count': sorry_count,
        'axiom_count': len(axiom_matches),
        'axiom_names': axiom_matches,
        'total_lines': total_lines,
        'tactic_counts': tactic_counts,
        'primary_technique': primary_technique,
    }


def infer_domain(imports: list[str], content: str) -> str:
    """Infer mathematical domain from imports and content."""
    nt_signals = ['Mathlib.NumberTheory', 'Mathlib.Data.ZMod', 'Nat.Prime',
                  'Mathlib.RingTheory', 'Mathlib.FieldTheory']
    algebra_signals = ['Mathlib.Algebra', 'Mathlib.GroupTheory', 'Mathlib.LinearAlgebra']
    combo_signals = ['Mathlib.Combinatorics', 'SimpleGraph', 'Finset.sym2', 'Hypergraph']
    analysis_signals = ['Mathlib.Analysis', 'Mathlib.MeasureTheory', 'Mathlib.Topology']

    scores = {'nt': 0, 'algebra': 0, 'combinatorics': 0, 'analysis': 0}
    for imp in imports:
        for signal in nt_signals:
            if signal in imp:
                scores['nt'] += 1
        for signal in algebra_signals:
            if signal in imp:
                scores['algebra'] += 1
        for signal in combo_signals:
            if signal in imp:
                scores['combinatorics'] += 1
        for signal in analysis_signals:
            if signal in imp:
                scores['analysis'] += 1

    if max(scores.values()) == 0:
        return 'nt'  # Default for this project
    return max(scores, key=scores.get)


def generate_findings(extracted: dict, slot: int, problem_id: str,
                      domain: str, filepath: str) -> list[dict]:
    """Generate finding records from extracted data."""
    findings = []

    is_proven = extracted['sorry_count'] == 0 and extracted['axiom_count'] == 0

    for decl in extracted['declarations']:
        if decl['type'] in ('theorem', 'lemma') and not decl['has_sorry']:
            findings.append({
                'finding_type': 'theorem',
                'domain_id': domain,
                'title': f"{decl['name']} ({decl['type']})",
                'description': f"Proven {decl['type']} from slot{slot}: {decl['statement'][:200]}",
                'problem_id': problem_id,
                'source_slot': slot,
                'source_file': filepath,
                'theorem_name': decl['name'],
                'theorem_statement': decl['statement'],
                'proof_technique': extracted['primary_technique'],
                'mathlib_imports': ', '.join(extracted['imports'][:10]),
                'proof_lines': decl['line_count'],
                'confidence': 'verified' if is_proven else 'medium',
                'tags': domain,
            })

    # If the whole file is proven, add a technique finding
    if is_proven and extracted['primary_technique']:
        findings.append({
            'finding_type': 'technique',
            'domain_id': domain,
            'title': f"Technique: {extracted['primary_technique']} (slot{slot})",
            'description': (
                f"Proof technique '{extracted['primary_technique']}' used successfully "
                f"in slot{slot} for problem {problem_id}. "
                f"Tactics: {', '.join(sorted(extracted['tactic_counts'].keys()))}. "
                f"Key imports: {', '.join(extracted['imports'][:5])}."
            ),
            'problem_id': problem_id,
            'source_slot': slot,
            'source_file': filepath,
            'proof_technique': extracted['primary_technique'],
            'mathlib_imports': ', '.join(extracted['imports'][:10]),
            'proof_lines': extracted['total_lines'],
            'confidence': 'verified',
            'tags': f"{domain},technique",
        })

    # If it failed (many sorry), add a failure finding
    if extracted['sorry_count'] > 2:
        findings.append({
            'finding_type': 'failure',
            'domain_id': domain,
            'title': f"Failed attempt: slot{slot} ({extracted['sorry_count']} sorry)",
            'description': (
                f"Aristotle attempt on {problem_id} in slot{slot} resulted in "
                f"{extracted['sorry_count']} sorry gaps out of "
                f"{len(extracted['declarations'])} declarations."
            ),
            'problem_id': problem_id,
            'source_slot': slot,
            'source_file': filepath,
            'why_failed': f"{extracted['sorry_count']} sorry remaining",
            'confidence': 'high',
            'tags': f"{domain},failure",
        })

    return findings


def insert_findings(db_path: str, findings: list[dict]) -> int:
    """Insert findings into knowledge.db. Returns count inserted."""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    inserted = 0

    for f in findings:
        try:
            cursor.execute("""
                INSERT INTO findings (
                    finding_type, domain_id, title, description, problem_id,
                    source_slot, source_file, theorem_name, theorem_statement,
                    proof_technique, mathlib_imports, proof_lines,
                    counterexample, why_failed, avoid_pattern,
                    confidence, tags, notes
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                f.get('finding_type'), f.get('domain_id'), f.get('title'),
                f.get('description'), f.get('problem_id'), f.get('source_slot'),
                f.get('source_file'), f.get('theorem_name'), f.get('theorem_statement'),
                f.get('proof_technique'), f.get('mathlib_imports'), f.get('proof_lines'),
                f.get('counterexample'), f.get('why_failed'), f.get('avoid_pattern'),
                f.get('confidence'), f.get('tags'), f.get('notes'),
            ))
            inserted += 1
        except sqlite3.IntegrityError as e:
            print(f"[math-forge] WARN: Skipping duplicate finding: {f['title']} ({e})",
                  file=sys.stderr)

    conn.commit()
    conn.close()
    return inserted


def main():
    parser = argparse.ArgumentParser(description='Extract findings from Aristotle result files')
    parser.add_argument('result_file', help='Path to .lean result file')
    parser.add_argument('--slot', type=int, help='Slot number (auto-detected from filename if omitted)')
    parser.add_argument('--problem-id', help='Problem ID (auto-detected from filename if omitted)')
    parser.add_argument('--db', default=None, help='Path to knowledge.db')
    args = parser.parse_args()

    filepath = Path(args.result_file)
    if not filepath.exists():
        print(f"[math-forge] ERROR: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)

    content = filepath.read_text()

    # Auto-detect slot from filename
    slot = args.slot
    if slot is None:
        slot_match = re.search(r'slot(\d+)', filepath.name)
        if slot_match:
            slot = int(slot_match.group(1))
        else:
            print("[math-forge] ERROR: Cannot detect slot number. Use --slot N.", file=sys.stderr)
            sys.exit(1)

    # Auto-detect problem ID from filename
    problem_id = args.problem_id
    if problem_id is None:
        # e.g., slot614_erdos_850_prime_factor_triples_result.lean -> erdos_850
        name_part = filepath.stem.replace(f'slot{slot}_', '').replace('_result', '')
        # Take first 2-3 segments as problem ID
        segments = name_part.split('_')
        if len(segments) >= 2:
            problem_id = '_'.join(segments[:3])
        else:
            problem_id = name_part

    # Resolve DB path
    db_path = args.db
    if db_path is None:
        plugin_root = Path(__file__).parent.parent
        db_path = str(plugin_root / 'data' / 'knowledge.db')

    # Ensure DB exists
    if not Path(db_path).exists():
        schema_path = Path(db_path).parent / 'schema.sql'
        if schema_path.exists():
            import subprocess
            subprocess.run(['sqlite3', db_path], stdin=open(schema_path), check=True)
            print(f"[math-forge] Created knowledge.db at {db_path}")
        else:
            print(f"[math-forge] ERROR: DB not found and no schema.sql available", file=sys.stderr)
            sys.exit(1)

    # Extract
    extracted = extract_from_lean(content, str(filepath))
    domain = infer_domain(extracted['imports'], content)

    # Generate findings
    findings = generate_findings(extracted, slot, problem_id, domain, str(filepath))

    if not findings:
        print(f"[math-forge] No findings extracted from {filepath.name}")
        return

    # Insert
    count = insert_findings(db_path, findings)

    # Update problem record
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    proven_count = sum(1 for f in findings if f['finding_type'] == 'theorem' and f['confidence'] == 'verified')
    failed_count = sum(1 for f in findings if f['finding_type'] == 'failure')

    status = 'proven' if extracted['sorry_count'] == 0 and extracted['axiom_count'] == 0 else 'partial'
    if extracted['sorry_count'] > 2:
        status = 'open'

    cursor.execute("""
        INSERT INTO problems (id, name, domain_id, status, submission_count, proven_count, failed_count, statement)
        VALUES (?, ?, ?, ?, 1, ?, ?, ?)
        ON CONFLICT(id) DO UPDATE SET
            submission_count = submission_count + 1,
            proven_count = proven_count + excluded.proven_count,
            failed_count = failed_count + excluded.failed_count,
            status = CASE WHEN excluded.status = 'proven' THEN 'proven' ELSE status END,
            updated_at = datetime('now')
    """, (problem_id, problem_id, domain, status, proven_count, failed_count, ''))

    conn.commit()
    conn.close()

    print(f"[math-forge] Extracted {count} findings from slot{slot} ({filepath.name})")
    print(f"  Declarations: {len(extracted['declarations'])}")
    print(f"  Sorry: {extracted['sorry_count']} | Axioms: {extracted['axiom_count']}")
    print(f"  Domain: {domain} | Technique: {extracted['primary_technique'] or 'unknown'}")
    print(f"  Imports: {len(extracted['imports'])}")


if __name__ == '__main__':
    main()
```

### Extraction Integration with /fetch

The extraction pipeline integrates with the existing `/fetch` command by adding a call at the end of Step 2 (after audit). The sketch command also integrates by calling `mk search` and `mk find` during Step 1b. Rather than modifying the existing `.claude/commands/` files directly in the plugin (which would require editing files outside the plugin directory), the integration is done through:

1. **Documentation in CLAUDE.md**: Add instructions for Claude to run extraction after fetch.
2. **PostToolUse hook on Bash**: A future hook can match Bash commands containing `aristotle_fetch` or `process-result` and trigger extraction automatically.
3. **Manual invocation**: `python3 math-forge/scripts/extract_findings.py <result_file>` after any fetch.

The recommended initial approach is to update the `/project:fetch` and `/project:process-result` command markdown files to include an extraction step at the end.

---

## Migration & Bootstrap

### scripts/migrate_tracking.py

One-time migration from tracking.db to seed knowledge.db with existing data.

```python
#!/usr/bin/env python3
"""migrate_tracking.py — Bootstrap knowledge.db from tracking.db.

Migrates:
    - proven_theorems -> findings (type: theorem)
    - false_lemmas -> findings (type: false_lemma)
    - failed_approaches -> findings (type: failure)
    - proof_techniques -> used to enrich technique fields
    - candidate_problems -> problems table

Does NOT migrate:
    - Raw .lean result files (too many; extract on-demand via extract_findings.py)
    - Submission metadata (stays in tracking.db as source of truth)
"""

import sqlite3
import sys
from pathlib import Path


def migrate(tracking_path: str, knowledge_path: str, schema_path: str):
    # Initialize knowledge.db
    if not Path(knowledge_path).exists():
        import subprocess
        subprocess.run(['sqlite3', knowledge_path], stdin=open(schema_path), check=True)
        print(f"[math-forge] Created knowledge.db")

    t_conn = sqlite3.connect(tracking_path)
    t_conn.row_factory = sqlite3.Row
    k_conn = sqlite3.connect(knowledge_path)

    t = t_conn.cursor()
    k = k_conn.cursor()

    count = 0

    # ---- 1. Migrate proven_theorems ----
    rows = t.execute("""
        SELECT pt.*, s.filename, s.problem_id, s.uuid
        FROM proven_theorems pt
        LEFT JOIN submissions s ON pt.submission_id = s.id
        WHERE pt.proof_complete = 1
    """).fetchall()

    for row in rows:
        slot = None
        filename = row['filename'] or ''
        import re
        slot_match = re.search(r'slot(\d+)', filename)
        if slot_match:
            slot = int(slot_match.group(1))

        try:
            k.execute("""
                INSERT OR IGNORE INTO findings (
                    finding_type, domain_id, title, description, problem_id,
                    source_slot, source_submission_uuid,
                    theorem_name, theorem_statement,
                    confidence, tags
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                'theorem', 'nt',  # Default domain; refined later
                f"{row['theorem_name']} ({row['theorem_type'] or 'theorem'})",
                f"Proven {row['theorem_type'] or 'theorem'}: {row['statement'] or row['theorem_name']}",
                row['problem_id'] or '',
                slot,
                row['uuid'],
                row['theorem_name'],
                row['statement'],
                'verified',
                'migrated',
            ))
            count += 1
        except sqlite3.IntegrityError:
            pass

    print(f"[math-forge] Migrated {count} proven theorems")

    # ---- 2. Migrate false_lemmas ----
    count2 = 0
    rows = t.execute("SELECT * FROM false_lemmas").fetchall()

    for row in rows:
        try:
            k.execute("""
                INSERT OR IGNORE INTO findings (
                    finding_type, domain_id, title, description, problem_id,
                    source_slot,
                    counterexample, why_failed, avoid_pattern,
                    confidence, tags
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                'false_lemma', 'combinatorics',  # Most false lemmas are from Tuza
                f"FALSE: {row['lemma_name']}",
                f"Disproven: {row['false_statement_english'] or row['false_statement']}",
                row['frontier_id'] or '',
                None,
                row['counterexample'],
                row['why_false'],
                row['avoid_pattern'],
                'disproven',
                f"false_lemma,{row['evidence_level']},migrated",
            ))
            count2 += 1
        except sqlite3.IntegrityError:
            pass

    print(f"[math-forge] Migrated {count2} false lemmas")

    # ---- 3. Migrate failed_approaches ----
    count3 = 0
    rows = t.execute("SELECT * FROM failed_approaches").fetchall()

    for row in rows:
        slot = None
        if row['submission_uuid']:
            slot_row = t.execute(
                "SELECT filename FROM submissions WHERE uuid=?",
                (row['submission_uuid'],)
            ).fetchone()
            if slot_row:
                slot_match = re.search(r'slot(\d+)', slot_row['filename'] or '')
                if slot_match:
                    slot = int(slot_match.group(1))

        try:
            k.execute("""
                INSERT OR IGNORE INTO findings (
                    finding_type, domain_id, title, description, problem_id,
                    source_slot, source_submission_uuid,
                    why_failed, avoid_pattern,
                    confidence, tags, notes
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                'failure', None,
                f"FAILED: {row['approach_name']}",
                row['approach_description'],
                row['problem_id'] or row['frontier_id'] or '',
                slot,
                row['submission_uuid'],
                row['why_failed'],
                row['avoid_pattern'],
                'high',
                f"failure,{row['failure_category'] or 'unknown'},migrated",
                row['learned_insight'],
            ))
            count3 += 1
        except sqlite3.IntegrityError:
            pass

    print(f"[math-forge] Migrated {count3} failed approaches")

    # ---- 4. Migrate candidate_problems -> problems ----
    count4 = 0
    rows = t.execute("SELECT * FROM candidate_problems").fetchall()

    for row in rows:
        domain_map = {
            'number_theory': 'nt', 'nt': 'nt', 'number-theory': 'nt',
            'algebra': 'algebra',
            'combinatorics': 'combinatorics',
            'analysis': 'analysis',
        }
        domain = domain_map.get(row['domain'], 'nt')

        try:
            k.execute("""
                INSERT OR IGNORE INTO problems (
                    id, name, domain_id, status,
                    submission_count, proven_count, failed_count,
                    statement
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                row['id'],
                row['name'],
                domain,
                row['status'] or 'open',
                row['submissions_count'] or 0,
                row['proven_count'] or 0,
                row['false_lemma_count'] or 0,
                row['statement'],
            ))
            count4 += 1
        except sqlite3.IntegrityError:
            pass

    print(f"[math-forge] Migrated {count4} candidate problems")

    k_conn.commit()
    k_conn.close()
    t_conn.close()

    total = count + count2 + count3 + count4
    print(f"\n[math-forge] Bootstrap complete: {total} total records migrated to knowledge.db")
    print(f"  Theorems: {count}")
    print(f"  False lemmas: {count2}")
    print(f"  Failed approaches: {count3}")
    print(f"  Problems: {count4}")


if __name__ == '__main__':
    plugin_root = Path(__file__).parent.parent
    tracking = str(plugin_root.parent / 'submissions' / 'tracking.db')
    knowledge = str(plugin_root / 'data' / 'knowledge.db')
    schema = str(plugin_root / 'data' / 'schema.sql')

    if len(sys.argv) > 1:
        tracking = sys.argv[1]
    if len(sys.argv) > 2:
        knowledge = sys.argv[2]

    migrate(tracking, knowledge, schema)
```

### Bootstrap Procedure

```bash
# 1. Initialize knowledge.db from schema
sqlite3 math-forge/data/knowledge.db < math-forge/data/schema.sql

# 2. Run migration from tracking.db
python3 math-forge/scripts/migrate_tracking.py

# 3. Verify
math-forge/scripts/mk stats
```

Expected yield: ~255 findings (114 proven theorems + 43 false lemmas + 56 failed approaches + 32 candidate problems = ~245 records, plus domain enrichment).

---

## Integration Points

### 1. /project:fetch Integration

After Step 2 (Deep audit), add:

```markdown
## Step 2b: Extract Knowledge (math-forge)

```bash
python3 math-forge/scripts/extract_findings.py \
    submissions/nu4_final/<result_file> \
    --slot <N> --problem-id <ID>
```

This automatically extracts findings into knowledge.db. If extraction fails, log a warning but do not block the fetch result.
```

### 2. /project:sketch Integration

During Step 1b (Check Database), supplement existing SQL queries with:

```markdown
### 1b-extended: Knowledge Base Check (math-forge)

```bash
# Search for related findings
math-forge/scripts/mk search "<problem keywords>"

# Get full problem context if we have it
math-forge/scripts/mk find "<problem_id>"

# Check failed approaches
math-forge/scripts/mk failed "<problem keywords>"
```

Use the output to populate a "## Prior Knowledge" section in the sketch:
```
## Prior Knowledge (auto-populated by math-forge)
- [PROVEN] <related theorem> via <technique> (slot N)
- [FAILED] <approach> — <why it failed> (slot M)
- No false lemmas for this problem
- Related technique: <technique> (used in <related problem>)
```
```

### 3. /project:process-result Integration

At the end of Step 5 (Update Database), add the same extraction call as `/fetch`.

### 4. SessionStart Hook

Automatically active when the plugin is loaded. No integration needed with existing commands -- the hook fires independently on session start.

### 5. PostToolUse Hook

Automatically active when the plugin is loaded. Fires on all Write/Edit operations on .lean files. No integration with existing commands needed.

### 6. mk CLI Availability

Add `math-forge/scripts` to PATH or invoke with full path. The `mk` script auto-resolves its DB path from `${CLAUDE_PLUGIN_ROOT}` when invoked from hooks, or from script-relative path when invoked directly.

For Claude to use `mk` during sessions, the plugin should set up the PATH via `CLAUDE_ENV_FILE` in the SessionStart hook:

```bash
# In context-loader.sh
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
    echo "export PATH=\"\$PATH:${PLUGIN_ROOT}/scripts\"" >> "$CLAUDE_ENV_FILE"
fi
```

---

## Performance Considerations

### FTS5 Indexing

- **Corpus size**: Expected ~500-2000 findings at maturity. FTS5 handles millions of rows; this is trivially small.
- **Query latency**: FTS5 MATCH queries on <10K rows: <1ms. sqlite3 process spawn: ~20ms. Total: <50ms.
- **Index size**: FTS5 index is ~2-3x the text size. At 500 findings averaging 200 bytes each: ~300KB total. Negligible.
- **Tokenizer**: `porter unicode61` handles English stemming. Mathematical notation (LaTeX, underscores) tokenizes imperfectly but structured field queries (`problem_id`, `theorem_name`) compensate.

### Hook Timeout Budget

| Hook | Budget | Expected | Components |
|------|--------|----------|------------|
| SessionStart | 5 sec | <2 sec | sqlite3 x2 queries + JSON formatting |
| PostToolUse (lean-validator) | 3 sec | <200ms | jq parse + grep x43 (false lemmas) + string compare |

SessionStart hook is the most expensive: two DB queries (tracking.db for queue, knowledge.db for stats) plus string formatting. No network calls (cached queue status). The python3 JSON escaping adds ~100ms.

### mk CLI Latency

All `mk` commands target <500ms. The bottleneck is bash startup + sqlite3 process spawn (~50ms combined). FTS5 queries themselves are <1ms on this corpus size. Verified against gpu-forge's `kb` script which achieves similar latency with 753 findings.

---

## Security & Data Integrity

### SQL Injection Prevention

All user input to `mk` CLI passes through `escape_sql()` which escapes single quotes. The FTS5 MATCH clause uses parameterized column-scoped queries (`{col1 col2}: query`) rather than raw string interpolation where possible. The Python extraction scripts use parameterized queries (`?` placeholders) exclusively.

### Data Validation

- **Finding insertion**: `finding_type` constrained by CHECK clause. `confidence` constrained by CHECK clause. `domain_id` is a REFERENCES constraint to `domains` table.
- **FTS5 consistency**: Three triggers (INSERT, DELETE, UPDATE) keep the FTS index synchronized with the `findings` table. External-content FTS table ensures the canonical data lives in `findings`, not the index.
- **Deduplication**: The migration script uses `INSERT OR IGNORE`. The extraction pipeline checks for existing slot-based findings before insertion. The `strategies` table has a `UNIQUE(problem_id, approach_name)` constraint.

### Backup Strategy

- `knowledge.db` is derived and reconstructible. If corrupted, delete it, re-run schema.sql, re-run migration, and re-extract from result files.
- `tracking.db` remains the source of truth. Never modified by math-forge.
- `knowledge.db` is gitignored (generated artifact). The schema.sql and migration scripts are committed.

### File Integrity

- The PostToolUse hook reads the `.lean` file to check for false lemma names. It uses grep with fixed strings, never eval or source. It never modifies the file.
- The extraction pipeline reads `.lean` files and writes to knowledge.db only. It never modifies source files.

---

## Questions & Answers

### Q1: Should the FTS5 table use content= (external content) or be self-contained?

**Decision: External content (`content=findings`).** The canonical data lives in the `findings` table with proper constraints and indexes. The FTS5 table is a derived search index. This means we need three sync triggers, but it keeps the architecture clean: `findings` is the source of truth, `findings_fts` is a search accelerator. If the FTS index corrupts, we can rebuild it with `INSERT INTO findings_fts(findings_fts) VALUES('rebuild')`.

### Q2: What BM25 weight distribution for FTS5 search?

**Decision: title=10, description=5, theorem_statement=5, proof_technique=3, tags=2, why_failed=3.** Title matches are most indicative of relevance (a search for "Erdos 364" should rank the Erdos 364 theorem highest). Statement and description carry the mathematical content. Technique and failure descriptions are supplementary. Tags are low-signal because they are short and categorical. `problem_id` is UNINDEXED because it is always queried with exact SQL LIKE, not FTS5 MATCH.

### Q3: Should `mk` use jq for JSON output or stick to formatted text?

**Decision: Formatted text for stdout, no JSON mode in MVP.** The primary consumers are (1) Claude reading Bash output and (2) Patrick glancing at terminal. Both parse formatted text well. JSON output mode can be added later with a `--json` flag if needed for programmatic consumption, but the priority is readable text output.

### Q4: How should the extraction pipeline handle duplicate slot extraction?

**Decision: Skip duplicates via INSERT OR IGNORE, plus slot-based check.** Before inserting findings, check if findings with the same `source_slot` already exist. If so, skip extraction. This handles the common case of re-fetching results or running extraction twice. The CHECK is done at the Python level (SELECT COUNT before INSERT) for clarity, backed by the database-level INSERT OR IGNORE as a safety net.

### Q5: Should knowledge.db live in `math-forge/data/` or `submissions/`?

**Decision: `math-forge/data/knowledge.db`.** Co-located with the plugin, consistent with gpu-forge pattern (`data/gpu_knowledge.db`). The `${CLAUDE_PLUGIN_ROOT}/data/` path is resolved by the hooks and `mk` script. This keeps knowledge.db logically grouped with its schema and scripts, separate from the tracking.db in `submissions/`.

### Q6: What tokenizer for FTS5?

**Decision: `porter unicode61`.** Porter stemming handles English well ("proving" matches "proof", "theorems" matches "theorem"). `unicode61` handles Unicode characters that appear in mathematical text. The alternative `trigram` tokenizer would allow substring matching (partial theorem names) but produces much larger indexes and slower queries. For a <2000 row corpus, the porter tokenizer with supplemental LIKE queries on structured fields is sufficient.

### Q7: Should the PostToolUse hook use `decision: "block"` for sorry replacement?

**Decision: Yes, but only for the specific case of Edit replacing proof code with sorry.** The hook checks: (a) the tool is Edit, (b) old_string contained proof content (by/exact/apply/simp/etc.), (c) new_string contains sorry where old_string did not. Only this specific pattern triggers a block. All other warnings (false lemma references) use advisory `additionalContext` without blocking, per UX spec guidance that blocking mid-task confuses the agent.

### Q8: How should the SessionStart hook handle knowledge.db not existing yet?

**Decision: Auto-initialize from schema.sql.** If `knowledge.db` doesn't exist, the hook runs `sqlite3 "$KNOWLEDGE_DB" < "${PLUGIN_ROOT}/data/schema.sql"` and continues with zero findings. This means the first session after plugin installation bootstraps the DB automatically. The migration script runs separately (manually or via `mk init`).

### Q9: Should `mk find` query tracking.db in addition to knowledge.db?

**Decision: Yes, cross-DB query.** `mk find` attaches tracking.db and queries submissions, false_lemmas, and failed_approaches tables directly. This provides the "single command, complete picture" UX goal without requiring all data to be duplicated in knowledge.db. The `mk` script opens both databases. knowledge.db is primary for findings/strategies; tracking.db is the fallback for submission-level data and the canonical source for false_lemmas.

### Q10: How should the plugin handle the PATH for mk?

**Decision: Use `CLAUDE_ENV_FILE` in SessionStart hook to add `${PLUGIN_ROOT}/scripts` to PATH.** This makes `mk search "query"` available as a bare command during the session, without requiring Claude to use the full path. The env file approach persists for the entire session. Fallback: Claude can always invoke `${CLAUDE_PLUGIN_ROOT}/scripts/mk search "query"` via full path.

### Q11: Should the queue_cache table be populated by the SessionStart hook or a separate refresh script?

**Decision: Separate refresh.** The SessionStart hook reads the cache table if populated, but does not populate it. Populating requires an Aristotle API call which adds latency and may fail. The `/project:status` command (existing) is the natural place to refresh the cache. The hook reads cached data only, keeping startup fast (<2 sec). If the cache is empty or stale (>6 hours), the hook notes this in the briefing.

### Q12: Should the migration be idempotent?

**Decision: Yes.** The migration script uses `INSERT OR IGNORE` for all records. It can be run multiple times safely. Each run reports counts of newly inserted records (which will be 0 on re-runs). This allows iterative migration as we add new source tables or improve extraction logic.

### Q13: How should `mk` handle the case where knowledge.db has zero findings (fresh install)?

**Decision: Graceful degradation with helpful hints.** `mk search` returns "No findings yet. Run `python3 math-forge/scripts/migrate_tracking.py` to bootstrap from tracking.db." `mk stats` shows zeros with the same hint. `mk init` runs schema creation + migration in one command.

### Q14: Should we add a `mk add` command for manual finding insertion?

**Decision: Not in MVP.** Per PM analysis. Primary ingestion paths are migration and extraction. Manual insertion creates data quality risk (inconsistent fields, missing provenance). If needed, direct SQL via sqlite3 is available for power users. Revisit for v2 if there is clear demand.

### Q15: How should the SubagentStart hook work (v2)?

**Decision: Deferred to v2.** When implemented, the hook will query knowledge.db for findings relevant to the subagent's task (extracted from the `agent_type` or task description), then inject up to 200 tokens of relevant findings via `additionalContext`. This prevents subagents from recommending already-failed approaches. The hook configuration is already structured to support this:

```json
{
  "event": "SubagentStart",
  "hooks": [{
    "type": "command",
    "command": "bash ${CLAUDE_PLUGIN_ROOT}/hooks/scripts/subagent-context.sh"
  }]
}
```
