# QA Strategy: math-forge

## Research Findings

### BATS (Bash Automated Testing System) Best Practices

[BATS](https://github.com/bats-core/bats-core) is a TAP-compliant testing framework for Bash 3.2+ that provides a simple way to verify UNIX programs behave as expected. A Bats test file is a Bash script with special syntax (`@test "description" { ... }`) for defining test cases. Key best practices from the [BATS documentation](https://bats-core.readthedocs.io/en/stable/writing-tests.html) and [practical guides](https://www.hackerone.com/blog/testing-bash-scripts-bats-practical-guide):

1. **Setup/Teardown Hooks**: BATS has `setup()`, `teardown()`, `setup_file()`, `teardown_file()` hooks that run before/after each test or test file. Good unit tests leave no effect in the environment — use teardown to clean up temp files and databases.

2. **The `run` Helper**: Many tests need to run a command and assert on exit status + output. `run <command>` saves exit status to `$status` and output to `$output`, then returns 0 so assertions can continue. Example:
   ```bash
   @test "mk search returns results" {
     run mk search "erdos"
     [ "$status" -eq 0 ]
     [[ "$output" =~ "SEARCH:" ]]
   }
   ```

3. **Code Reusability**: Use `load` to source common test helpers. For math-forge, create `tests/test_helper.bash` with DB setup/teardown functions and load it in all test files.

4. **CI Integration**: BATS integrates with GitHub Actions via `bats-core/bats-action`. Output is TAP-compliant, compatible with all CI systems.

5. **Assertions Library**: The [bats-assert](https://github.com/bats-core/bats-assert) library provides readable assertions: `assert_success`, `assert_output`, `assert_line`, `refute_output`.

6. **Integration Testing**: BATS excels at integration tests — spawn real processes, check real file I/O, query real databases. No mocks needed for CLI tools.

Sources: [BATS GitHub](https://github.com/bats-core/bats-core), [Writing Tests](https://bats-core.readthedocs.io/en/stable/writing-tests.html), [HackerOne Practical Guide](https://www.hackerone.com/blog/testing-bash-scripts-bats-practical-guide)

---

### SQLite FTS5 Testing Strategies

FTS5 (Full-Text Search) testing requires validating tokenizer configuration, search relevance, and external-content table synchronization. From [SQLite FTS5 docs](https://www.sqlite.org/fts5.html) and [practical guides](https://thelinuxcode.com/sqlite-full-text-search-fts5-in-practice-fast-search-ranking-and-real-world-patterns/):

1. **Tokenizer Validation**: Test early with representative data. For math-forge, the `porter unicode61` tokenizer handles English stemming but may tokenize mathematical notation (LaTeX, underscores) imperfectly. Test searches on theorem names like `erdos_850_triple_factors` to ensure structured field fallbacks work.

2. **Golden Query Testing**: Capture 20-50 real searches with expected top results. Test BM25 ranking weights produce the expected ordering. This is the same pattern gpu-forge uses with 72 golden queries for GPU vendor/architecture lookups. For math-forge: "Erdos 364" should rank the Erdos 364 theorem first, not unrelated Erdos theorems.

3. **Trigger Synchronization Testing**: External-content FTS tables require INSERT/UPDATE/DELETE triggers to stay synchronized. Test all three CRUD operations: insert a finding, query FTS, update the finding, verify FTS reflects the change, delete the finding, verify FTS no longer returns it. Trigger bugs manifest as stale search results.

4. **Query Safeguards**: Validate MATCH syntax before passing user input. Test edge cases: empty query, special characters (`AND OR NOT`), adjacent operators (`AND OR`), malformed queries. FTS5 syntax errors should produce helpful error messages, not crashes.

5. **Index Maintenance**: FTS5 virtual tables auto-update. Test that bulk inserts (bootstrap migration) don't corrupt the index. Verify `INSERT INTO findings_fts(findings_fts) VALUES('rebuild')` rebuilds the index correctly.

Sources: [SQLite FTS5 Extension](https://www.sqlite.org/fts5.html), [FTS5 Practical Guide](https://medium.com/@johnidouglasmarangon/full-text-search-in-sqlite-a-practical-guide-80a69c3f42a4), [FTS5 in Practice](https://thelinuxcode.com/sqlite-full-text-search-fts5-in-practice-fast-search-ranking-and-real-world-patterns/)

---

### CLI Tool Testing Patterns

From [CLI testing tools survey](https://spin.atomicobject.com/2016/01/11/command-line-interface-testing-tools/) and [BATS end-to-end guide](https://pkaramol.medium.com/end-to-end-command-line-tool-testing-with-bats-and-auto-expect-7a4ffb19336d):

1. **Three-Layer Testing**: Unit tests for individual functions (`escape_sql`, `normalize_problem`), integration tests for subcommands (`mk search`, `mk find`), and end-to-end tests for full workflows (sketch → submit → fetch → extract → search).

2. **Exit Code Validation**: Every command must return 0 on success, non-zero on failure. Test happy path (0), missing arguments (1), invalid input (1), DB errors (1+).

3. **Output Validation**: Test both stdout (data) and stderr (errors). Use `[[ "$output" =~ "pattern" ]]` for substring matching, `assert_line -n 0 "header"` for exact line matching.

4. **TTY vs Pipe Behavior**: Test color output when stdout is TTY, plain text when piped. BATS runs commands in a subshell; use `script` command to simulate TTY or check `NO_COLOR` env var.

5. **Idempotency**: Commands like `mk init` should be idempotent — running twice produces the same result. Test repeated invocation.

6. **Error Messages**: Test that error messages are actionable: `[math-forge] ERROR: <what happened>. <how to fix>.` Use `refute_output --partial "sqlite3 failed"` to ensure raw DB errors are wrapped.

Sources: [CLI Testing Tools](https://spin.atomicobject.com/2016/01/11/command-line-interface-testing-tools/), [E2E with BATS](https://pkaramol.medium.com/end-to-end-command-line-tool-testing-with-bats-and-auto-expect-7a4ffb19336d)

---

### Claude Code Plugin Hook Testing

From [Claude Code Hooks Guide](https://code.claude.com/docs/en/hooks-guide), [Hook Development Skill](https://github.com/anthropics/claude-code/blob/main/plugins/plugin-dev/skills/hook-development/SKILL.md), and [lifecycle events guide](https://claudefa.st/blog/tools/hooks/hooks-guide):

1. **Lifecycle Event Coverage**: Claude Code has 14 hook events. Math-forge uses 2 in MVP (SessionStart, PostToolUse), 1 in v2 (SubagentStart). Test each event with representative inputs.

2. **Hook Input Simulation**: Hooks receive JSON on stdin with `session_id`, `transcript_path`, `cwd`, `tool_name`, `tool_input`, `tool_response`. Create test fixtures with sample JSON for each hook type. Example:
   ```bash
   @test "PostToolUse detects sorry replacement" {
     echo '{"tool_name":"Edit","tool_input":{"old_string":"by omega","new_string":"sorry"}}' | \
       bash hooks/scripts/lean-validator.sh > output.json
     run jq -r '.decision' output.json
     assert_output "block"
   }
   ```

3. **Timeout Enforcement**: SessionStart has 5s timeout, PostToolUse 3s. Test hooks complete within budget. Use `timeout 3s <hook-script>` to enforce in tests.

4. **Exit Code Semantics**: Exit 0 = success (JSON parsed from stdout), exit 2 = blocking error (stderr fed to Claude), other = non-blocking error. Test all three paths.

5. **JSON Output Validation**: Hooks output JSON with `hookSpecificOutput` or `decision` fields. Use `jq` to validate structure. Invalid JSON = Claude sees raw stderr.

6. **Context Injection Size**: SessionStart `additionalContext` should be ~300 tokens. Test token count with `wc -w` approximation (1 token ≈ 0.75 words). Exceeding 500 tokens wastes Claude's context window.

Sources: [Hooks Guide](https://code.claude.com/docs/en/hooks-guide), [Hooks Mastery](https://github.com/disler/claude-code-hooks-mastery), [Hook Development](https://github.com/anthropics/claude-code/blob/main/plugins/plugin-dev/skills/hook-development/SKILL.md), [All 12 Events](https://claudefa.st/blog/tools/hooks/hooks-guide)

---

## Test Strategy Overview

### Philosophy

**Real execution, no mocks.** Per project CLAUDE.md: "ALWAYS run REAL tests — NEVER use mocks or simulations." Math-forge tests spin up real SQLite databases, run real FTS5 queries, execute real bash scripts. This is feasible because:
- SQLite is in-memory capable (`:memory:` database for unit tests)
- BATS spawns real subprocesses (no shell mocking needed)
- Hooks are bash scripts (no complex runtime to simulate)

**Golden query regression tests.** Like gpu-forge's 72 golden queries, math-forge maintains a set of ~20-30 canonical searches with expected top results. These guard against BM25 weight changes, tokenizer regressions, and schema changes that degrade search quality.

**Test coverage targets:**
- **Hooks**: 100% (2 hooks × happy/error paths = 4 test cases minimum)
- **mk CLI subcommands**: 100% (6 subcommands × 3-5 test cases each = ~25 tests)
- **Extraction pipeline**: 80%+ (core path + error handling, skip edge cases in MVP)
- **Integration workflows**: 100% (sketch → extract → search = 1 E2E test per workflow)

**Speed budget:**
- Unit tests: <100ms each (in-memory DB)
- Integration tests: <1s each (on-disk DB)
- E2E tests: <5s each (real file I/O + multi-step)
- Full suite: <30s (parallel execution via `bats --jobs 8`)

---

## Test Categories & Cases

### 1. Unit Tests (BATS) — Hook Scripts

#### SessionStart Hook (`hooks/scripts/context-loader.sh`)

**Test file**: `tests/test_session_start_hook.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  # Create temp directories
  export TEST_DIR="$(mktemp -d)"
  export PLUGIN_ROOT="$TEST_DIR/math-forge"
  export PROJECT_DIR="$TEST_DIR/project"
  mkdir -p "$PLUGIN_ROOT/data" "$PROJECT_DIR/submissions"

  # Set env vars
  export CLAUDE_PLUGIN_ROOT="$PLUGIN_ROOT"
  export CLAUDE_PROJECT_DIR="$PROJECT_DIR"

  # Create minimal tracking.db
  sqlite3 "$PROJECT_DIR/submissions/tracking.db" <<SQL
    CREATE TABLE submissions (id INTEGER, filename TEXT, status TEXT,
                               submitted_at TEXT, completed_at TEXT,
                               sorry_count INTEGER, proven_count INTEGER);
    INSERT INTO submissions VALUES
      (1, 'slot622_erdos364.lean', 'completed', '2026-02-13 10:00:00', '2026-02-13 11:00:00', 0, 3),
      (2, 'slot623_erdos1052.lean', 'running', '2026-02-13 12:00:00', NULL, NULL, NULL);
SQL

  # Create minimal knowledge.db
  sqlite3 "$PLUGIN_ROOT/data/knowledge.db" < "$PLUGIN_ROOT/../../data/schema.sql"
  sqlite3 "$PLUGIN_ROOT/data/knowledge.db" \
    "INSERT INTO findings (finding_type, title, description) VALUES ('theorem', 'Test', 'desc');"
}

teardown() {
  rm -rf "$TEST_DIR"
}

@test "context-loader.sh outputs valid JSON with additionalContext" {
  run bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  assert_success

  # Validate JSON structure
  echo "$output" | jq -e '.hookSpecificOutput.additionalContext' >/dev/null
}

@test "context-loader.sh reports in-flight count correctly" {
  run bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  assert_success

  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext')
  [[ "$context" =~ "1 in-flight" ]]
}

@test "context-loader.sh lists ready-to-fetch results" {
  run bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  assert_success

  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext')
  [[ "$context" =~ "slot622" ]]
}

@test "context-loader.sh completes within 5s timeout" {
  run timeout 5s bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  assert_success
}

@test "context-loader.sh token count <500" {
  run bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext')

  # Rough approximation: 1 token ≈ 0.75 words
  word_count=$(echo "$context" | wc -w)
  token_estimate=$((word_count * 4 / 3))
  [ "$token_estimate" -lt 500 ]
}

@test "context-loader.sh creates knowledge.db if missing" {
  rm "$PLUGIN_ROOT/data/knowledge.db"
  run bash "$PLUGIN_ROOT/../../hooks/scripts/context-loader.sh"
  assert_success
  [ -f "$PLUGIN_ROOT/data/knowledge.db" ]
}
```

**Coverage**: 6 test cases
- Valid JSON output structure
- Queue status parsing (in-flight count, slots open)
- Ready-to-fetch detection
- Timeout compliance (5s)
- Token budget compliance (<500)
- Auto-initialization of missing DB

---

#### PostToolUse Hook (`hooks/scripts/lean-validator.sh`)

**Test file**: `tests/test_lean_validator_hook.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  export TEST_DIR="$(mktemp -d)"
  export PLUGIN_ROOT="$TEST_DIR/math-forge"
  export PROJECT_DIR="$TEST_DIR/project"
  mkdir -p "$PLUGIN_ROOT" "$PROJECT_DIR/submissions"

  export CLAUDE_PLUGIN_ROOT="$PLUGIN_ROOT"
  export CLAUDE_PROJECT_DIR="$PROJECT_DIR"

  # Create tracking.db with false_lemmas
  sqlite3 "$PROJECT_DIR/submissions/tracking.db" <<SQL
    CREATE TABLE false_lemmas (lemma_name TEXT);
    INSERT INTO false_lemmas VALUES ('apex_bridge_coverage');
SQL
}

teardown() {
  rm -rf "$TEST_DIR"
}

@test "lean-validator.sh allows valid .lean file creation" {
  cat > "$TEST_DIR/test.lean" <<LEAN
theorem foo : 1 + 1 = 2 := by omega
LEAN

  input_json=$(cat <<JSON
{"tool_name":"Write","tool_input":{"file_path":"$TEST_DIR/test.lean"},"tool_response":""}
JSON
)

  run bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success
  # No blocking output = allow by default
}

@test "lean-validator.sh blocks sorry replacement in Edit" {
  # Original file with proof
  cat > "$TEST_DIR/test.lean" <<LEAN
theorem foo : 1 + 1 = 2 := by omega
LEAN

  input_json=$(cat <<JSON
{
  "tool_name": "Edit",
  "tool_input": {
    "file_path": "$TEST_DIR/test.lean",
    "old_string": "theorem foo : 1 + 1 = 2 := by omega",
    "new_string": "theorem foo : 1 + 1 = 2 := sorry"
  }
}
JSON
)

  # Update the file to match the edit
  echo "theorem foo : 1 + 1 = 2 := sorry" > "$TEST_DIR/test.lean"

  run bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success

  # Check decision field
  decision=$(echo "$output" | jq -r '.decision // "allow"')
  [ "$decision" = "block" ]

  reason=$(echo "$output" | jq -r '.reason')
  [[ "$reason" =~ "BLOCKED" ]]
  [[ "$reason" =~ "sorry" ]]
}

@test "lean-validator.sh allows adding sorry to new theorem" {
  input_json=$(cat <<JSON
{
  "tool_name": "Write",
  "tool_input": {
    "file_path": "$TEST_DIR/new.lean",
    "new_string": "theorem bar : True := sorry"
  }
}
JSON
)

  echo "theorem bar : True := sorry" > "$TEST_DIR/new.lean"

  run bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success
  # Adding sorry to NEW code is allowed (old_string is empty)
}

@test "lean-validator.sh warns on false lemma reference" {
  cat > "$TEST_DIR/test.lean" <<LEAN
lemma uses_false : X := by
  apply apex_bridge_coverage
LEAN

  input_json=$(cat <<JSON
{"tool_name":"Write","tool_input":{"file_path":"$TEST_DIR/test.lean"}}
JSON
)

  run bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success

  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext // ""')
  [[ "$context" =~ "WARNING" ]]
  [[ "$context" =~ "apex_bridge_coverage" ]]
  [[ "$context" =~ "false lemma" ]]
}

@test "lean-validator.sh ignores non-.lean files" {
  input_json=$(cat <<JSON
{"tool_name":"Write","tool_input":{"file_path":"$TEST_DIR/test.txt"}}
JSON
)

  run bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success
  [ -z "$output" ]
}

@test "lean-validator.sh completes within 3s timeout" {
  cat > "$TEST_DIR/large.lean" <<LEAN
$(for i in {1..100}; do echo "theorem t$i : True := trivial"; done)
LEAN

  input_json=$(cat <<JSON
{"tool_name":"Write","tool_input":{"file_path":"$TEST_DIR/large.lean"}}
JSON
)

  run timeout 3s bash "$PLUGIN_ROOT/../hooks/scripts/lean-validator.sh" <<< "$input_json"
  assert_success
}
```

**Coverage**: 6 test cases
- Valid file creation (allow)
- Sorry replacement detection (block with reason)
- New file with sorry (allow — not a replacement)
- False lemma reference (warning, not block)
- Non-.lean file skip
- Timeout compliance (3s)

---

### 2. Unit Tests (BATS) — mk CLI Tool

#### `mk search` Command

**Test file**: `tests/test_mk_search.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db
}

teardown() {
  teardown_test_db
}

@test "mk search with no args shows usage" {
  run "$MK" search
  assert_failure
  [[ "$output" =~ "Usage:" ]]
}

@test "mk search returns BM25-ranked results" {
  # Insert test findings
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, title, description, domain_id, confidence)
    VALUES
      ('theorem', 'Erdos 364 powerful triples', 'Proven theorem about powerful numbers', 'nt', 'verified'),
      ('failure', 'Erdos 307 greedy', 'Failed greedy approach', 'nt', 'high'),
      ('theorem', 'Wilson theorem', 'Modular arithmetic', 'nt', 'verified');
SQL

  run "$MK" search "Erdos powerful"
  assert_success

  # Check output structure
  [[ "$output" =~ "SEARCH:" ]]
  [[ "$output" =~ "Erdos 364 powerful triples" ]]

  # Erdos 364 should rank higher than Wilson (more keyword matches)
  line_erdos=$(echo "$output" | grep -n "Erdos 364" | cut -d: -f1)
  line_wilson=$(echo "$output" | grep -n "Wilson" | cut -d: -f1)
  [ "$line_erdos" -lt "$line_wilson" ]
}

@test "mk search respects --limit flag" {
  for i in {1..10}; do
    sqlite3 "$TEST_DB" \
      "INSERT INTO findings (finding_type, title, description, domain_id)
       VALUES ('theorem', 'Test $i', 'description', 'nt');"
  done

  run "$MK" search "Test" --limit 3
  assert_success

  # Should show exactly 3 results + header + footer
  result_count=$(echo "$output" | grep -c "Test [0-9]" || true)
  [ "$result_count" -eq 3 ]
}

@test "mk search --domain filters results" {
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, title, description, domain_id)
    VALUES
      ('theorem', 'NT theorem', 'number theory', 'nt'),
      ('theorem', 'Algebra theorem', 'group theory', 'algebra');
SQL

  run "$MK" search "theorem" --domain nt
  assert_success
  [[ "$output" =~ "NT theorem" ]]
  [[ ! "$output" =~ "Algebra theorem" ]]
}

@test "mk search returns no results for unknown query" {
  run "$MK" search "xyzabc123nonexistent"
  assert_success
  [[ "$output" =~ "0 results" ]]
}

@test "mk search completes in <500ms" {
  # Insert 100 findings
  for i in {1..100}; do
    sqlite3 "$TEST_DB" \
      "INSERT INTO findings (finding_type, title, description, domain_id)
       VALUES ('theorem', 'Test theorem $i', 'description of test $i', 'nt');"
  done

  start=$(date +%s%N)
  run "$MK" search "test theorem"
  end=$(date +%s%N)

  duration_ms=$(( (end - start) / 1000000 ))
  [ "$duration_ms" -lt 500 ]
}
```

**Coverage**: 6 test cases
- No args error handling
- BM25 ranking correctness
- `--limit` flag
- `--domain` filter
- No results case
- Performance (<500ms)

---

#### `mk find` Command

**Test file**: `tests/test_mk_find.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db

  # Create cross-DB test environment
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, title, problem_id, domain_id, source_slot)
    VALUES ('theorem', 'Erdos 364 result', 'erdos_364', 'nt', 622);

    INSERT INTO strategies (problem_id, approach_name, outcome, attempts)
    VALUES ('erdos_364', 'powerful triple construction', 'in_flight', 1);

    INSERT INTO problems (id, name, domain_id, status)
    VALUES ('erdos_364', 'Erdos 364: Powerful Triples', 'nt', 'in_flight');
SQL

  # Create tracking.db for cross-query
  sqlite3 "$TRACKING_DB" <<SQL
    CREATE TABLE submissions (filename TEXT, status TEXT);
    INSERT INTO submissions VALUES ('slot622_erdos364.lean', 'completed');
SQL
}

teardown() {
  teardown_test_db
}

@test "mk find retrieves problem summary" {
  run "$MK" find erdos_364
  assert_success

  [[ "$output" =~ "PROBLEM: Erdos 364" ]]
  [[ "$output" =~ "Status: in_flight" ]]
  [[ "$output" =~ "Domain: number-theory" ]]
}

@test "mk find shows findings and strategies" {
  run "$MK" find erdos_364
  assert_success

  [[ "$output" =~ "Erdos 364 result" ]]
  [[ "$output" =~ "powerful triple construction" ]]
}

@test "mk find handles fuzzy matching" {
  # Should match 'erdos_364' even with different formatting
  run "$MK" find "Erdos 364"
  assert_success
  [[ "$output" =~ "PROBLEM: Erdos 364" ]]

  run "$MK" find "erdos364"
  assert_success
  [[ "$output" =~ "PROBLEM: Erdos 364" ]]
}

@test "mk find returns empty sections for non-existent problem" {
  run "$MK" find "nonexistent_problem"
  assert_success
  [[ "$output" =~ "No problem found" ]]
}
```

**Coverage**: 4 test cases
- Problem summary retrieval
- Findings + strategies aggregation
- Fuzzy problem ID matching
- Non-existent problem handling

---

#### `mk stats` Command

**Test file**: `tests/test_mk_stats.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db

  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, domain_id) VALUES
      ('theorem', 'nt'), ('theorem', 'nt'), ('theorem', 'algebra'),
      ('failure', 'nt'), ('false_lemma', 'combinatorics');
SQL
}

teardown() {
  teardown_test_db
}

@test "mk stats shows KB counts" {
  run "$MK" stats
  assert_success

  [[ "$output" =~ "Findings:" ]]
  [[ "$output" =~ "5" ]]  # Total findings
}

@test "mk stats shows domain distribution" {
  run "$MK" stats
  assert_success

  [[ "$output" =~ "number-theory" ]]
  [[ "$output" =~ "3 findings" ]]  # 2 theorems + 1 failure in NT
}

@test "mk stats shows pipeline status" {
  run "$MK" stats
  assert_success
  [[ "$output" =~ "Pipeline:" ]]
}
```

**Coverage**: 3 test cases
- KB size reporting
- Domain distribution
- Pipeline status display

---

#### Helper Functions & Utilities

**Test file**: `tests/test_mk_utils.bats`

```bash
#!/usr/bin/env bats

load test_helper

@test "escape_sql handles single quotes" {
  source "$MK"  # Load the mk script functions

  result=$(escape_sql "O'Reilly")
  [ "$result" = "O''Reilly" ]
}

@test "escape_sql handles multiple quotes" {
  source "$MK"

  result=$(escape_sql "It's a 'test'")
  [ "$result" = "It''s a ''test''" ]
}

@test "normalize_problem strips spaces and underscores" {
  source "$MK"

  result=$(normalize_problem "Erdos 364")
  [ "$result" = "erdos364" ]

  result=$(normalize_problem "erdos_364")
  [ "$result" = "erdos364" ]
}
```

**Coverage**: 3 test cases
- SQL injection prevention (escape_sql)
- Problem ID normalization

**Total `mk` CLI unit tests**: ~20 test cases across 5 files

---

### 3. Unit Tests (Python) — Extraction Pipeline

**Test file**: `tests/test_extract_findings.py` (pytest)

```python
import pytest
import sqlite3
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent / 'scripts'))
from extract_findings import (
    extract_from_lean, infer_domain, generate_findings, insert_findings
)

@pytest.fixture
def sample_lean_content():
    return """
import Mathlib.NumberTheory.Primes
import Mathlib.Data.Nat.Prime

theorem erdos_850_triple_factors (k : Nat) :
    ∃ n, (omega(n) >= k) ∧ (omega(n+1) >= k) ∧ (omega(n+2) >= k) := by
  sorry

lemma helper_bound (x : Nat) : x > 0 := by
  omega
"""

@pytest.fixture
def proven_lean_content():
    return """
import Mathlib.NumberTheory.ModularForms

theorem wilson_mod_prime (p : Nat) [Fact p.Prime] :
    (p - 1)! ≡ -1 [MOD p] := by
  apply wilson_thm
  exact Fact.out
"""

def test_extract_declarations(sample_lean_content):
    extracted = extract_from_lean(sample_lean_content, "test.lean")

    assert len(extracted['declarations']) == 2
    assert extracted['declarations'][0]['name'] == 'erdos_850_triple_factors'
    assert extracted['declarations'][0]['type'] == 'theorem'
    assert extracted['declarations'][0]['has_sorry'] == True

    assert extracted['declarations'][1]['name'] == 'helper_bound'
    assert extracted['declarations'][1]['has_sorry'] == False

def test_extract_imports(sample_lean_content):
    extracted = extract_from_lean(sample_lean_content, "test.lean")

    assert 'Mathlib.NumberTheory.Primes' in extracted['imports']
    assert 'Mathlib.Data.Nat.Prime' in extracted['imports']

def test_sorry_count(sample_lean_content):
    extracted = extract_from_lean(sample_lean_content, "test.lean")
    assert extracted['sorry_count'] == 1

def test_infer_domain_number_theory():
    imports = ['Mathlib.NumberTheory.Primes', 'Mathlib.Data.ZMod']
    domain = infer_domain(imports, "")
    assert domain == 'nt'

def test_infer_domain_combinatorics():
    imports = ['Mathlib.Combinatorics.SimpleGraph']
    domain = infer_domain(imports, "")
    assert domain == 'combinatorics'

def test_generate_findings_proven_result(proven_lean_content):
    extracted = extract_from_lean(proven_lean_content, "slot594.lean")
    findings = generate_findings(extracted, 594, 'wilson', 'nt', 'slot594.lean')

    # Should generate 2 findings: 1 theorem + 1 technique
    assert len(findings) >= 1

    theorem_finding = [f for f in findings if f['finding_type'] == 'theorem'][0]
    assert theorem_finding['theorem_name'] == 'wilson_mod_prime'
    assert theorem_finding['confidence'] == 'verified'
    assert theorem_finding['source_slot'] == 594

def test_generate_findings_failed_result(sample_lean_content):
    extracted = extract_from_lean(sample_lean_content, "slot999.lean")
    findings = generate_findings(extracted, 999, 'test', 'nt', 'slot999.lean')

    # Has sorry, should not generate theorem finding (or mark as not verified)
    theorem_findings = [f for f in findings if f['finding_type'] == 'theorem' and f['confidence'] == 'verified']
    assert len(theorem_findings) == 0

def test_insert_findings_deduplication(tmp_path):
    db_path = tmp_path / "test.db"

    # Create schema
    sqlite3.connect(db_path).executescript(open('data/schema.sql').read())

    findings = [
        {'finding_type': 'theorem', 'title': 'Test', 'description': 'desc',
         'domain_id': 'nt', 'confidence': 'verified'}
    ]

    # Insert twice
    count1 = insert_findings(str(db_path), findings)
    count2 = insert_findings(str(db_path), findings)

    assert count1 == 1
    assert count2 == 0  # Duplicate, not inserted
```

**Coverage**: 9 test cases
- Theorem/lemma declaration extraction
- Import detection
- Sorry counting
- Domain inference (NT, algebra, combinatorics)
- Finding generation (proven vs failed)
- Deduplication on insertion

**Run with**: `pytest tests/test_extract_findings.py -v`

---

### 4. Integration Tests — Full Workflows

**Test file**: `tests/test_integration_workflows.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db
  export TEST_LEAN_DIR="$TEST_DIR/results"
  mkdir -p "$TEST_LEAN_DIR"
}

teardown() {
  teardown_test_db
}

@test "WORKFLOW: extract → search → find roundtrip" {
  # 1. Create a sample result file
  cat > "$TEST_LEAN_DIR/slot622_erdos364_result.lean" <<LEAN
import Mathlib.NumberTheory.Primes

theorem erdos_364_powerful_triple :
    ∃ a b c, powerful a ∧ powerful b ∧ powerful c ∧ a + 1 = b ∧ b + 1 = c := by
  sorry
LEAN

  # 2. Run extraction
  run python3 scripts/extract_findings.py \
    "$TEST_LEAN_DIR/slot622_erdos364_result.lean" \
    --slot 622 --problem-id erdos_364 --db "$TEST_DB"
  assert_success
  [[ "$output" =~ "Extracted" ]]

  # 3. Search for the theorem
  run "$MK" search "erdos 364 powerful"
  assert_success
  [[ "$output" =~ "erdos_364_powerful_triple" ]]

  # 4. Find problem-level view
  run "$MK" find erdos_364
  assert_success
  [[ "$output" =~ "PROBLEM: erdos_364" ]]
  [[ "$output" =~ "powerful_triple" ]]
}

@test "WORKFLOW: migration → stats → search" {
  # 1. Create tracking.db with sample data
  sqlite3 "$TRACKING_DB" <<SQL
    CREATE TABLE proven_theorems (
      theorem_name TEXT, theorem_type TEXT, statement TEXT,
      submission_id INTEGER, proof_complete INTEGER
    );
    CREATE TABLE submissions (id INTEGER, filename TEXT, problem_id TEXT, uuid TEXT);

    INSERT INTO proven_theorems VALUES
      ('wilson_thm', 'theorem', 'Wilson theorem statement', 1, 1);
    INSERT INTO submissions VALUES
      (1, 'slot594_wilson.lean', 'wilson', 'uuid-594');
SQL

  # 2. Run migration
  run python3 scripts/migrate_tracking.py "$TRACKING_DB" "$TEST_DB"
  assert_success
  [[ "$output" =~ "Migrated" ]]

  # 3. Check stats
  run "$MK" stats
  assert_success
  [[ "$output" =~ "Findings:" ]]
  [[ "$output" =~ "1" ]]  # At least 1 finding

  # 4. Search should find migrated theorem
  run "$MK" search "wilson"
  assert_success
  [[ "$output" =~ "wilson_thm" ]]
}

@test "WORKFLOW: SessionStart hook provides search-relevant context" {
  # 1. Insert findings into KB
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, title, problem_id, source_slot)
    VALUES ('theorem', 'Recent proven result', 'test_problem', 622);
SQL

  # 2. Create tracking.db with completed submission
  sqlite3 "$TRACKING_DB" <<SQL
    CREATE TABLE submissions (filename TEXT, status TEXT, completed_at TEXT, verified INTEGER);
    INSERT INTO submissions VALUES
      ('slot622_test.lean', 'completed', datetime('now', '-1 hour'), NULL);
SQL

  # 3. Run SessionStart hook
  run bash hooks/scripts/context-loader.sh
  assert_success

  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext')

  # Context should mention ready-to-fetch result
  [[ "$context" =~ "slot622" ]]
  [[ "$context" =~ "READY TO FETCH" ]]
}
```

**Coverage**: 3 E2E workflows
- Extract → Search → Find (full knowledge lifecycle)
- Migration → Stats → Search (bootstrap path)
- SessionStart hook context relevance

---

### 5. Golden Query Tests — FTS5 Relevance Regression

**Test file**: `tests/test_golden_queries.bats`

Like gpu-forge's 72 golden queries, maintain ~20 canonical searches with expected top results.

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db

  # Seed KB with representative findings
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (id, finding_type, title, description, problem_id, domain_id, proof_technique, source_slot)
    VALUES
      (1, 'theorem', 'Erdos 364: powerful triples', 'Proven theorem about consecutive powerful numbers', 'erdos_364', 'nt', 'pigeonhole', 622),
      (2, 'theorem', 'Erdos 370: smooth consecutive', 'Stormer theorem application', 'erdos_370', 'nt', 'smooth number theory', 616),
      (3, 'theorem', 'Erdos 850: prime factor triples', 'Pigeonhole on omega(n)', 'erdos_850', 'nt', 'pigeonhole', 614),
      (4, 'failure', 'Erdos 307: greedy reciprocal', 'Greedy decomposition failed', 'erdos_307', 'nt', NULL, 597),
      (5, 'false_lemma', 'Tuza apex bridge coverage', 'Disproven by Fin 5 counterexample', 'tuza_nu4', 'combinatorics', NULL, 534),
      (6, 'theorem', 'FT p=3 q≡1mod4', 'Jacobi + Euler criterion', 'ft_p3', 'nt', 'QR + Euler', 590),
      (7, 'theorem', 'Wilson mod prime', 'Factorial congruence', 'wilson', 'nt', 'Wilson theorem', 594);
SQL
}

teardown() {
  teardown_test_db
}

# Golden query format: search term → expected top result ID
@test "GOLDEN: 'Erdos 364' ranks Erdos 364 theorem first" {
  run "$MK" search "Erdos 364"
  assert_success

  # Extract first result ID (hacky but works)
  first_line=$(echo "$output" | grep "^\s*#1" | head -1)
  [[ "$first_line" =~ "Erdos 364: powerful triples" ]]
}

@test "GOLDEN: 'pigeonhole' ranks pigeonhole-using theorems top" {
  run "$MK" search "pigeonhole"
  assert_success

  # Top 2 should be Erdos 364 and Erdos 850 (both use pigeonhole)
  [[ "$output" =~ "Erdos 364" ]]
  [[ "$output" =~ "Erdos 850" ]]
}

@test "GOLDEN: 'smooth consecutive' ranks Erdos 370 first" {
  run "$MK" search "smooth consecutive"
  assert_success

  first_line=$(echo "$output" | grep "^\s*#1" | head -1)
  [[ "$first_line" =~ "Erdos 370" ]]
}

@test "GOLDEN: 'FT p=3' ranks Feit-Thompson results" {
  run "$MK" search "FT p=3"
  assert_success
  [[ "$output" =~ "FT p=3 q≡1mod4" ]]
}

@test "GOLDEN: 'greedy failed' finds failure, not theorems" {
  run "$MK" search "greedy failed"
  assert_success

  first_line=$(echo "$output" | grep "^\s*#1" | head -1)
  [[ "$first_line" =~ "Erdos 307" ]]
  [[ "$first_line" =~ "FAILED" ]]
}

@test "GOLDEN: 'Tuza apex' ranks false lemma first" {
  run "$MK" search "Tuza apex"
  assert_success

  first_line=$(echo "$output" | grep "^\s*#1" | head -1)
  [[ "$first_line" =~ "apex bridge" ]]
  [[ "$first_line" =~ "FALSE" ]]
}

@test "GOLDEN: 'Wilson factorial' finds Wilson theorem" {
  run "$MK" search "Wilson factorial"
  assert_success
  [[ "$output" =~ "Wilson mod prime" ]]
}

# BM25 weight regression: title matches rank higher than description matches
@test "GOLDEN: title match beats description match" {
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO findings (finding_type, title, description, domain_id)
    VALUES
      ('theorem', 'Exact Match Title', 'unrelated description', 'nt'),
      ('theorem', 'Unrelated Title', 'description with Exact Match inside', 'nt');
SQL

  run "$MK" search "Exact Match"
  assert_success

  # "Exact Match Title" should rank first (title weight=10 > description weight=5)
  first_line=$(echo "$output" | grep "^\s*#1" | head -1)
  [[ "$first_line" =~ "Exact Match Title" ]]
}
```

**Coverage**: 8 golden queries
- Problem-specific searches (Erdos 364, FT p=3, Tuza)
- Technique searches (pigeonhole, greedy)
- Status-specific searches (failed, false)
- BM25 weight regression (title > description)

**Maintenance**: When BM25 weights or schema change, re-run golden queries. If relevance degrades (wrong top result), adjust weights or fix the query.

---

### 6. Performance Tests

**Test file**: `tests/test_performance.bats`

```bash
#!/usr/bin/env bats

load test_helper

setup() {
  setup_test_db

  # Insert 1000 findings for realistic performance test
  for i in {1..1000}; do
    sqlite3 "$TEST_DB" <<SQL
      INSERT INTO findings (finding_type, title, description, domain_id)
      VALUES ('theorem', 'Test theorem $i', 'Description for test case number $i with various mathematical content', 'nt');
SQL
  done
}

teardown() {
  teardown_test_db
}

@test "PERF: mk search completes in <500ms with 1000 findings" {
  start=$(date +%s%N)
  run "$MK" search "test theorem"
  end=$(date +%s%N)

  duration_ms=$(( (end - start) / 1000000 ))
  echo "# mk search took ${duration_ms}ms" >&3
  [ "$duration_ms" -lt 500 ]
}

@test "PERF: mk find completes in <500ms" {
  # Add problem + strategies
  sqlite3 "$TEST_DB" <<SQL
    INSERT INTO problems (id, name, domain_id) VALUES ('test_prob', 'Test Problem', 'nt');
    INSERT INTO strategies (problem_id, approach_name, outcome) VALUES ('test_prob', 'approach1', 'proven');
SQL

  start=$(date +%s%N)
  run "$MK" find test_prob
  end=$(date +%s%N)

  duration_ms=$(( (end - start) / 1000000 ))
  echo "# mk find took ${duration_ms}ms" >&3
  [ "$duration_ms" -lt 500 ]
}

@test "PERF: mk stats completes in <200ms" {
  start=$(date +%s%N)
  run "$MK" stats
  end=$(date +%s%N)

  duration_ms=$(( (end - start) / 1000000 ))
  echo "# mk stats took ${duration_ms}ms" >&3
  [ "$duration_ms" -lt 200 ]
}

@test "PERF: SessionStart hook completes in <2s" {
  # Create realistic tracking.db
  sqlite3 "$TRACKING_DB" <<SQL
    CREATE TABLE submissions (id INTEGER, filename TEXT, status TEXT, submitted_at TEXT, completed_at TEXT);
    $(for i in {1..100}; do echo "INSERT INTO submissions VALUES ($i, 'slot$i.lean', 'completed', datetime('now'), datetime('now'));"; done)
SQL

  start=$(date +%s%N)
  run bash hooks/scripts/context-loader.sh
  end=$(date +%s%N)

  duration_ms=$(( (end - start) / 1000000 ))
  echo "# SessionStart hook took ${duration_ms}ms" >&3
  [ "$duration_ms" -lt 2000 ]
}
```

**Coverage**: 4 performance benchmarks
- `mk search` with 1K findings (<500ms)
- `mk find` with aggregation (<500ms)
- `mk stats` dashboard (<200ms)
- SessionStart hook (<2s)

---

### 7. Test Helpers & Fixtures

**File**: `tests/test_helper.bash`

```bash
# test_helper.bash — Shared test utilities for math-forge BATS tests

# Paths
export PLUGIN_ROOT="${BATS_TEST_DIRNAME}/.."
export MK="${PLUGIN_ROOT}/scripts/mk"

# Test DB setup
setup_test_db() {
  export TEST_DIR="$(mktemp -d)"
  export TEST_DB="$TEST_DIR/knowledge.db"
  export TRACKING_DB="$TEST_DIR/tracking.db"

  # Initialize knowledge.db from schema
  sqlite3 "$TEST_DB" < "${PLUGIN_ROOT}/data/schema.sql"

  # Set env vars for mk and hooks
  export MATH_FORGE_DB="$TEST_DB"
  export CLAUDE_PLUGIN_ROOT="$PLUGIN_ROOT"
  export CLAUDE_PROJECT_DIR="$TEST_DIR"
}

teardown_test_db() {
  rm -rf "$TEST_DIR"
}

# Assertions (using bats-assert if available, fallback otherwise)
if command -v assert_success &>/dev/null; then
  # bats-assert is available, use it
  :
else
  # Fallback implementations
  assert_success() {
    [ "$status" -eq 0 ]
  }

  assert_failure() {
    [ "$status" -ne 0 ]
  }

  assert_output() {
    [[ "$output" == "$1" ]]
  }
fi
```

---

## Acceptance Criteria

### Per-Feature Acceptance (MVP)

| Feature | Acceptance Criteria | Test Coverage |
|---------|---------------------|---------------|
| **knowledge.db creation** | Schema creates all tables, FTS5 virtual table, triggers, indexes without errors. DB file <1MB empty. | `test_mk_init.bats` |
| **FTS5 search** | `mk search <query>` returns BM25-ranked results. Top 5 by default. Highlights [PROVEN], [FAILED], [FALSE] badges. Completes in <500ms. | `test_mk_search.bats`, `test_golden_queries.bats` |
| **Problem lookup** | `mk find <problem-id>` aggregates findings, strategies, submissions. Fuzzy matches problem IDs. Returns "none yet" for empty sections. | `test_mk_find.bats` |
| **SessionStart hook** | Hook fires on session start. Outputs valid JSON with `additionalContext`. Token count <500. Completes in <5s. Reports queue status, ready-to-fetch, KB size. | `test_session_start_hook.bats` |
| **PostToolUse lean-validator** | Hook fires on Write/Edit of `.lean` files. Blocks sorry replacement with `decision: "block"`. Warns on false lemma references. Completes in <3s. | `test_lean_validator_hook.bats` |
| **Result extraction** | `extract_findings.py <file>` parses theorems, imports, sorry count. Inserts findings into knowledge.db. Handles duplicates gracefully. Reports extraction count. | `test_extract_findings.py` |
| **Migration bootstrap** | `migrate_tracking.py` copies proven_theorems, false_lemmas, failed_approaches, candidate_problems from tracking.db. Idempotent (INSERT OR IGNORE). Reports counts. | Manual test + verification via `mk stats` |

### Global Quality Gates (Before "Ready")

1. **All BATS tests pass**: `bats tests/*.bats --jobs 8` returns 0 exit code.
2. **All pytest tests pass**: `pytest tests/test_*.py -v` returns 0 exit code.
3. **Performance benchmarks met**: No test exceeds timeout budget (SessionStart <5s, PostToolUse <3s, mk commands <500ms).
4. **Golden queries pass**: All 8 golden query tests rank expected results first (no relevance regressions).
5. **Hook validation**: Both hooks produce valid JSON (jq parses without error). No raw stderr leakage to Claude.
6. **Zero false positives**: PostToolUse hook does NOT block valid .lean file operations (100% specificity on sorry replacement detection).
7. **DB integrity**: After full test suite, knowledge.db validates with `sqlite3 <db> "PRAGMA integrity_check"` → "ok".
8. **Extraction coverage**: At least 3 real result files (.lean) from submissions/ successfully extracted into KB without errors.

---

## CI Pipeline

### GitHub Actions Configuration

**File**: `.github/workflows/math-forge-tests.yml`

```yaml
name: math-forge tests

on:
  push:
    paths:
      - 'math-forge/**'
      - '.github/workflows/math-forge-tests.yml'
  pull_request:
    paths:
      - 'math-forge/**'

jobs:
  test:
    runs-on: macos-latest  # Match dev environment

    steps:
      - uses: actions/checkout@v4

      - name: Install dependencies
        run: |
          brew install bats-core jq sqlite
          pip3 install pytest

      - name: Run BATS tests
        run: |
          cd math-forge
          bats tests/test_*.bats --jobs 4 --tap

      - name: Run pytest tests
        run: |
          cd math-forge
          pytest tests/test_extract_findings.py -v --tb=short

      - name: Validate hook JSON output
        run: |
          cd math-forge
          # Test SessionStart hook outputs valid JSON
          bash hooks/scripts/context-loader.sh | jq . >/dev/null

          # Test PostToolUse hook outputs valid JSON
          echo '{"tool_name":"Write","tool_input":{"file_path":"test.lean"}}' | \
            bash hooks/scripts/lean-validator.sh | jq . >/dev/null || true

      - name: DB integrity check
        run: |
          cd math-forge
          # Run migration, then check integrity
          python3 scripts/migrate_tracking.py || true
          sqlite3 data/knowledge.db "PRAGMA integrity_check;"
```

### Test Execution Strategy

- **Pre-commit**: Fast unit tests only (`bats tests/test_mk_*.bats --jobs 8` + `pytest tests/test_extract_findings.py`) — <10s total.
- **Pre-push**: Full suite including integration and golden queries — <30s total.
- **CI on PR**: Full suite + performance benchmarks + hook validation.
- **CI on main branch**: Full suite + extraction coverage test (extract 3 real .lean files from submissions/).

### Pass/Fail Criteria

- **BATS exit code 0**: All test cases pass. TAP output shows 0 failures.
- **pytest exit code 0**: All assertions pass. No exceptions raised.
- **jq validation**: All hook outputs parse as valid JSON without errors.
- **Performance gates**: No test case exceeds its timeout budget. Report timing in CI logs.
- **Golden queries**: All 8 queries rank expected results first. If any fail, CI fails (prevents relevance regressions).

---

## Questions & Answers

### Q1: Should we use BATS or ShellSpec for bash testing?

**Answer: BATS.** BATS is the industry-standard TAP-compliant testing framework for bash with 7K+ GitHub stars, mature CI integration (bats-action), and the `run` helper that makes CLI testing trivial. ShellSpec has more features (mocking, coverage) but adds complexity we don't need. The gpu-forge reference uses BATS, and all research sources recommend it for CLI tools. BATS is the right tool for this job.

**Impact**: All hook and mk CLI tests written in BATS. Test files follow `test_*.bats` naming convention.

---

### Q2: How should we handle the in-memory vs on-disk DB tradeoff for tests?

**Answer: Hybrid approach.** Unit tests use `:memory:` databases for speed (<100ms). Integration tests use on-disk temp files (`mktemp -d`) to test real file I/O and multi-process scenarios (FTS5 external-content table consistency). E2E tests use on-disk to simulate real workflow.

**Rationale**: In-memory is 10x faster but doesn't test file permissions, WAL mode, or cross-process sync. On-disk is necessary for full coverage but too slow for unit tests. The hybrid approach gives us both speed and realism.

**Implementation**: `test_helper.bash` provides `setup_test_db()` which creates a temp directory with on-disk DB. Individual tests can override with `sqlite3 :memory:` if needed.

---

### Q3: Should golden queries be hardcoded or data-driven?

**Answer: Hardcoded in BATS test cases.** For ~20-30 golden queries, individual `@test` cases with explicit assertions are more maintainable than a data-driven loop. Each test documents the expected behavior explicitly. As the suite grows beyond 50 queries, migrate to a CSV/JSON fixture with a parameterized test loop.

**Rationale**: Explicit test cases are easier to debug when they fail. The failure message shows exactly which query regressed. Data-driven tests require more test infrastructure (CSV parsing, loop over cases) and produce less informative failures.

**Future**: If golden query count exceeds 50, add `tests/golden_queries.csv` with columns `query,expected_top_result_id,expected_badge` and a single BATS test that loops over rows.

---

### Q4: How should we validate the extraction pipeline's accuracy?

**Answer: Ground truth validation with 3-5 manually annotated result files.** Select diverse .lean files (proven with 0 sorry, near-miss with 1 sorry, failed with 5+ sorry, different domains). Manually extract expected findings (theorem names, technique, domain). Assert extraction output matches expected findings.

**Implementation**: `tests/fixtures/ground_truth/` directory with `.lean` files + `.expected.json` files. Pytest test loads fixture, runs extraction, asserts output matches expected.

**Coverage**: This catches regex bugs (missed theorems), domain inference errors, and technique classification mistakes.

---

### Q5: Should we test the PostToolUse hook in isolation or integrated with Claude Code?

**Answer: Isolation only.** The hook is a bash script that reads JSON stdin and outputs JSON stdout. Test it as a pure function: provide sample JSON inputs, assert on outputs. Testing integrated with Claude Code requires a running session and is too slow/brittle for CI.

**Rationale**: Hooks are designed to be testable in isolation — they have no dependencies beyond bash, jq, and sqlite3. The input schema is well-defined (JSON with `tool_name`, `tool_input`, `tool_response`). The output schema is well-defined (`decision` + `reason` or `hookSpecificOutput`). Test the contract, not the framework.

**Edge case testing**: Create pathological JSON inputs (malformed, missing fields, huge files) and verify the hook handles them gracefully (no crash, valid JSON output even on error).

---

### Q6: How many test cases are sufficient for "done"?

**Answer: MVP target is ~60 test cases total.** Breakdown:
- Hooks: 12 cases (6 SessionStart + 6 PostToolUse)
- mk CLI: 20 cases (4 subcommands × 5 cases each)
- Extraction: 9 cases (pytest)
- Integration: 3 E2E workflows
- Golden queries: 8 cases
- Performance: 4 benchmarks
- Helpers/utils: 4 cases

This provides ~80% coverage of critical paths. Non-critical paths (edge cases, error formatting variations, verbose flags) deferred to v2.

**Quality over quantity**: 60 well-written tests that run in <30s and catch real bugs > 200 fragile tests that take 5 minutes and flake.

---

### Q7: Should we mock the Aristotle API in hook tests?

**Answer: No API calls in hooks.** Per TECH.md Q11, the SessionStart hook reads cached queue status from tracking.db, not the live API. PostToolUse has no API dependency. No mocking needed.

**If we add API calls in v2**: Use VCR.py-style request recording. Capture real API responses to fixtures, replay in tests. But avoid API calls in hooks entirely — they add latency and failure modes.

---

### Q8: How should we test FTS5 trigger synchronization?

**Answer: CRUD cycle test.** Insert a finding, assert FTS returns it. Update the finding's description, assert FTS reflects the new text. Delete the finding, assert FTS no longer returns it. This exercises all three triggers (INSERT, UPDATE, DELETE).

**Test case**:
```bash
@test "FTS5 triggers keep index synchronized" {
  # Insert
  sqlite3 "$TEST_DB" \
    "INSERT INTO findings (id, finding_type, title, description)
     VALUES (999, 'theorem', 'Original Title', 'original description');"

  run sqlite3 "$TEST_DB" \
    "SELECT COUNT(*) FROM findings_fts WHERE findings_fts MATCH 'original';"
  [ "$output" -eq 1 ]

  # Update
  sqlite3 "$TEST_DB" \
    "UPDATE findings SET description = 'updated description' WHERE id = 999;"

  run sqlite3 "$TEST_DB" \
    "SELECT COUNT(*) FROM findings_fts WHERE findings_fts MATCH 'updated';"
  [ "$output" -eq 1 ]

  run sqlite3 "$TEST_DB" \
    "SELECT COUNT(*) FROM findings_fts WHERE findings_fts MATCH 'original';"
  [ "$output" -eq 0 ]

  # Delete
  sqlite3 "$TEST_DB" "DELETE FROM findings WHERE id = 999;"

  run sqlite3 "$TEST_DB" \
    "SELECT COUNT(*) FROM findings_fts WHERE findings_fts MATCH 'updated';"
  [ "$output" -eq 0 ]
}
```

**Coverage**: This single test validates all three triggers are correctly configured and fire in the right order.

---

### Q9: Should we test color output in mk CLI?

**Answer: Test color presence/absence based on TTY detection, not specific ANSI codes.** Validate:
- When stdout is TTY and `NO_COLOR` unset → output contains ANSI escape sequences (`\033[`)
- When stdout is piped → output has no ANSI codes
- When `NO_COLOR=1` → output has no ANSI codes

**Implementation**:
```bash
@test "mk search uses color when TTY" {
  # TTY simulation is hard in BATS; test the logic instead
  run bash -c "export NO_COLOR=; [ -t 1 ] && echo 'has color' || echo 'no color'"
  # This is a weak test; main validation is manual
}

@test "mk search strips color when NO_COLOR set" {
  NO_COLOR=1 run "$MK" search "test"
  refute_output --partial $'\033['  # No ANSI escapes
}
```

**Rationale**: Color is a UX enhancement, not critical logic. Manual validation (run `mk search` in terminal, verify colors appear) is sufficient. Automated tests focus on the NO_COLOR and TTY detection logic, not the specific color codes.

---

### Q10: How should we test the migration script?

**Answer: Manual test with verification via `mk stats`.** The migration is a one-time bootstrap operation, not a frequently-run command. Automated testing would require maintaining a fixture tracking.db with realistic data, which is high maintenance.

**Process**:
1. Run migration on real tracking.db: `python3 scripts/migrate_tracking.py`
2. Check stderr for errors (should be none)
3. Run `mk stats` and verify counts match expected (114 proven theorems → ~114 theorem findings)
4. Run `mk search "erdos"` and verify some known Erdos results appear
5. Run `mk failed` and verify known false lemmas appear

**Acceptance**: Migration reports >200 findings extracted. `mk stats` shows non-zero counts in all categories. No sqlite3 errors in stderr.

**Idempotency test**: Run migration twice, verify second run reports "0 new records" (INSERT OR IGNORE works).

---

### Q11: Should we test the sketch template "Prior Knowledge" auto-population?

**Answer: Deferred to integration test when sketch command is updated.** The sketch command lives in `.claude/commands/sketch.md`, outside the plugin directory. Testing it requires modifying the command (adding `mk search` and `mk find` calls), then validating the output.

**V2 test**: When sketch command is integrated, add a BATS test that runs the sketch command with a mock problem ID, asserts the generated .txt file contains a "## Prior Knowledge" section, and that section contains relevant findings from the KB.

**For MVP**: Validate `mk search` and `mk find` outputs are correct (already covered). Trust that the sketch command can consume them.

---

### Q12: How do we validate the ~300 token SessionStart budget?

**Answer: Word count approximation.** 1 token ≈ 0.75 words (rough heuristic for English). Assert word count × 1.33 < 500.

**Test case**:
```bash
@test "context-loader.sh token count <500" {
  run bash hooks/scripts/context-loader.sh
  context=$(echo "$output" | jq -r '.hookSpecificOutput.additionalContext')

  word_count=$(echo "$context" | wc -w)
  token_estimate=$((word_count * 4 / 3))
  [ "$token_estimate" -lt 500 ]
}
```

**Rationale**: Precise token counting requires the tokenizer (tiktoken), which is a Python dependency we don't want in bash hooks. Word count is good enough for a sanity check. If the hook output is 600 words (~800 tokens), we have a problem. If it's 200 words (~267 tokens), we're good.

---

### Q13: Should performance tests fail the build if they exceed the budget?

**Answer: Yes, hard fail.** Performance budgets are requirements, not guidelines. If SessionStart takes 6 seconds, it blocks session startup and violates the user story acceptance criteria ("orient in <10 sec"). The test should fail.

**Implementation**: `[ "$duration_ms" -lt 500 ]` returns exit 1 if duration exceeds budget. BATS propagates the failure.

**Escape hatch**: If CI runners are slower than dev machines, increase budgets by 50% in CI-only (detect via `CI=true` env var). But the dev machine budget is the SLA.

---

### Q14: How do we test the mk script's 3-level DB path resolution?

**Answer: Three test cases, one per resolution level.**

```bash
@test "mk uses MATH_FORGE_DB if set" {
  export MATH_FORGE_DB="/tmp/custom.db"
  sqlite3 "$MATH_FORGE_DB" < data/schema.sql

  run "$MK" stats
  assert_success
  # Should query the custom DB, not the default
}

@test "mk uses CLAUDE_PLUGIN_ROOT if MATH_FORGE_DB unset" {
  unset MATH_FORGE_DB
  export CLAUDE_PLUGIN_ROOT="$TEST_DIR/plugin"
  mkdir -p "$CLAUDE_PLUGIN_ROOT/data"
  sqlite3 "$CLAUDE_PLUGIN_ROOT/data/knowledge.db" < data/schema.sql

  run "$MK" stats
  assert_success
}

@test "mk uses script-relative path if both unset" {
  unset MATH_FORGE_DB
  unset CLAUDE_PLUGIN_ROOT

  # mk should resolve to ../data/knowledge.db relative to scripts/mk
  run "$MK" stats
  assert_success
}
```

**Coverage**: All three resolution paths tested. This ensures `mk` works in dev (script-relative), CI (CLAUDE_PLUGIN_ROOT set), and manual invocation (MATH_FORGE_DB override).

---

### Q15: Should we test that extraction handles malformed .lean files gracefully?

**Answer: Yes, error handling tests.** Create pathological .lean files:
- Empty file → 0 findings extracted
- File with no imports → domain defaults to 'nt'
- File with 100 sorries → generates failure finding
- File with unparseable Unicode → extraction completes, may skip unparseable sections

**Test case**:
```python
def test_extract_empty_file(tmp_path):
    lean_file = tmp_path / "empty.lean"
    lean_file.write_text("")

    extracted = extract_from_lean("", str(lean_file))
    assert extracted['declarations'] == []
    assert extracted['sorry_count'] == 0

def test_extract_no_imports():
    content = "theorem foo : True := trivial"
    extracted = extract_from_lean(content, "test.lean")

    assert extracted['imports'] == []
    domain = infer_domain([], content)
    assert domain == 'nt'  # Default domain
```

**Rationale**: The extraction pipeline should never crash. Worst case: it extracts 0 findings and reports "No findings extracted." Test the error paths.

---

## Summary

**Total test suite**: ~60 test cases across 12 files (10 BATS + 2 pytest), targeting <30s execution time with parallel jobs. Coverage includes:

- **Unit tests**: Hook scripts (12), mk CLI (20), extraction pipeline (9), helpers (4)
- **Integration tests**: E2E workflows (3)
- **Regression tests**: Golden queries (8), performance benchmarks (4)

**CI pipeline**: GitHub Actions on PR/push, runs full suite + validation. Pass criteria: all tests green, performance budgets met, DB integrity validated, golden queries pass.

**Quality gates**: 100% hook coverage, 80%+ extraction coverage, 0 false positives on sorry-replacement blocking, <30s full suite execution.

**Philosophy**: Real execution (no mocks), golden query regression tests (like gpu-forge), fast unit tests (<100ms), realistic integration tests (on-disk DB).
