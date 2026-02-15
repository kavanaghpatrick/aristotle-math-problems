# math-forge: Technical Design

## Architecture

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

         extract_findings.py
              |
    .lean result files --> parsed --> findings inserted
```

## Plugin Structure

```
math-forge/
+-- .claude-plugin/
|   +-- plugin.json
+-- data/
|   +-- schema.sql
|   +-- knowledge.db          (gitignored)
+-- hooks/
|   +-- hooks.json
|   +-- scripts/
|       +-- context-loader.sh
|       +-- lean-validator.sh
+-- scripts/
|   +-- mk
|   +-- extract_findings.py
|   +-- migrate_tracking.py
+-- skills/
+-- commands/
+-- agents/
+-- tests/
    +-- test_helper.bash
    +-- test_*.bats
    +-- test_*.py
    +-- fixtures/
```

## Database Schema (knowledge.db)

### Tables

**domains** -- Mathematical classification taxonomy
- `id TEXT PRIMARY KEY` -- 'nt', 'algebra', 'combinatorics', 'analysis'
- `name TEXT NOT NULL`
- `description TEXT`
- Pre-populated with 4 rows

**findings** -- Core knowledge atoms
- `id INTEGER PRIMARY KEY AUTOINCREMENT`
- `finding_type TEXT NOT NULL` -- CHECK: theorem, technique, failure, false_lemma, computation, mathlib_api, insight
- `domain_id TEXT REFERENCES domains(id)`
- `title TEXT NOT NULL`, `description TEXT NOT NULL`, `problem_id TEXT`
- Source: `source_slot INTEGER`, `source_submission_uuid TEXT`, `source_file TEXT`
- Proof: `theorem_name TEXT`, `theorem_statement TEXT`, `proof_technique TEXT`, `mathlib_imports TEXT`, `proof_lines INTEGER`
- Failure: `counterexample TEXT`, `why_failed TEXT`, `avoid_pattern TEXT`
- `confidence TEXT` -- CHECK: verified, high, medium, low, disproven
- `created_at TEXT`, `updated_at TEXT`, `tags TEXT`, `notes TEXT`

**strategies** -- Problem-level approach tracking
- `id INTEGER PRIMARY KEY AUTOINCREMENT`
- `problem_id TEXT NOT NULL`, `problem_name TEXT NOT NULL`, `domain_id TEXT`
- `approach_name TEXT NOT NULL`, `approach_description TEXT`
- `outcome TEXT NOT NULL` -- CHECK: proven, partial, failed, in_flight, untried
- `submission_slot INTEGER`, `submission_uuid TEXT`, `finding_ids TEXT`
- `attempts INTEGER DEFAULT 1`, `last_attempted TEXT`, `learned TEXT`
- `UNIQUE(problem_id, approach_name)`

**problems** -- Problem-level summary
- `id TEXT PRIMARY KEY`, `name TEXT NOT NULL`, `domain_id TEXT`
- `status TEXT` -- CHECK: open, proven, partial, false, in_flight
- `submission_count INTEGER`, `proven_count INTEGER`, `failed_count INTEGER`
- `statement TEXT`, `best_result TEXT`

**queue_cache** -- Aristotle queue status (singleton)
- `id INTEGER PRIMARY KEY CHECK(id = 1)`
- `cached_at TEXT`, `in_flight INTEGER`, `slots_open INTEGER`
- `ready_to_fetch TEXT`, `recently_completed TEXT`, `top_near_miss TEXT`, `raw_json TEXT`

### FTS5 Virtual Table

```sql
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
```

BM25 weights: `title=10, description=5, theorem_name=1, theorem_statement=5, proof_technique=3, tags=2, why_failed=3`

### Sync Triggers

Three triggers keep FTS5 in sync: `findings_fts_insert` (AFTER INSERT), `findings_fts_delete` (AFTER DELETE), `findings_fts_update` (AFTER UPDATE -- delete old then insert new).

### Indexes (11)

findings: type, domain, problem, slot, confidence, created_at
strategies: problem, outcome, domain
problems: domain, status

### Views (4)

`v_proven_techniques`, `v_failed_approaches`, `v_problem_dashboard`, `v_near_miss_findings`

## Hook Configurations

### hooks/hooks.json

```json
{
  "description": "Math-forge lifecycle hooks: session briefing, Lean file validation",
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

## CLI Tool (`mk`)

Bash script (~350 lines). 3-level DB path resolution: `MATH_FORGE_DB` env > `${CLAUDE_PLUGIN_ROOT}/data/knowledge.db` > script-relative.

Subcommands: search, find, strategies, failed, stats, init, help

Key functions: `escape_sql()`, `run_sql()`, `normalize_problem()`

TTY-aware color: green=proven, red=failed, yellow=in-flight, cyan=headers. Gated on `[ -t 1 ] && [ -z "${NO_COLOR:-}" ]`.

## Performance Budgets

| Component | Budget | Expected |
|-----------|--------|----------|
| SessionStart hook | 5 sec | <2 sec |
| PostToolUse hook | 3 sec | <200ms |
| mk search | 500ms | <50ms |
| mk find | 500ms | <100ms |
| mk stats | 200ms | <50ms |

## Data Flow

1. **Session start**: context-loader.sh queries tracking.db + knowledge.db, outputs ~300 token briefing as JSON additionalContext
2. **Sketch writing**: Claude invokes `mk search` and `mk find` for relevant prior findings
3. **Result processing**: After `/fetch`, extract_findings.py parses .lean file, inserts findings
4. **Lean validation**: lean-validator.sh fires on Write|Edit of .lean files, checks sorry replacement and false lemma refs
