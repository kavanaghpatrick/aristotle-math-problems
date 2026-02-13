# Tasks: math-forge

## Phase 1: Foundation (devops + database)

- [x] 1.1 Create plugin directory structure
  - **Do**: Create the complete math-forge plugin directory tree at `/Users/patrickkavanagh/math/math-forge/`: `.claude-plugin/`, `data/`, `hooks/scripts/`, `scripts/`, `skills/`, `commands/`, `agents/`, `tests/fixtures/`. Add `.gitkeep` in empty dirs.
  - **Files**: `math-forge/` directory tree
  - **Done when**: All directories exist
  - **Verify**: `test -d math-forge/.claude-plugin && test -d math-forge/data && test -d math-forge/hooks/scripts && test -d math-forge/scripts && test -d math-forge/tests/fixtures && echo PASS`
  - **Commit**: `feat(devops): create math-forge plugin directory structure`

- [x] 1.2 Write plugin.json manifest
  - **Do**: Create `math-forge/.claude-plugin/plugin.json` with name "math-forge", version "0.1.0", description about mathematical knowledge infrastructure, author "Patrick Kavanagh".
  - **Files**: `math-forge/.claude-plugin/plugin.json`
  - **Done when**: Valid JSON with name, version, description, author
  - **Verify**: `python3 -c "import json; json.load(open('math-forge/.claude-plugin/plugin.json'))"`
  - **Commit**: `feat(devops): add plugin.json manifest`

- [x] 1.3 Write database schema with FTS5
  - **Do**: Create `math-forge/data/schema.sql` with the complete knowledge.db schema. Read TECH.md at `/Users/patrickkavanagh/math/ai/tasks/spec/TECH.md` for the full SQL. Must include: PRAGMAs (WAL, foreign_keys), `domains` table (4 seed rows: nt, algebra, combinatorics, analysis), `findings` table (CHECK constraints on finding_type: theorem/technique/failure/false_lemma/computation/mathlib_api/insight; confidence: verified/high/medium/low/disproven; columns for provenance, proof details, failure details), `strategies` table (outcome CHECK: proven/partial/failed/in_flight/untried), `problems` table (status CHECK: open/partial/proven/disproven/abandoned), `queue_cache` table, FTS5 virtual table `findings_fts` (content=findings, content_rowid=id, tokenize='porter unicode61', columns: title, description, problem_id UNINDEXED, theorem_name, theorem_statement, proof_technique, tags, why_failed), 3 FTS5 sync triggers, 11 indexes, 4 views (v_proven_techniques, v_failed_approaches, v_problem_dashboard, v_near_miss_findings).
  - **Files**: `math-forge/data/schema.sql`
  - **Done when**: `sqlite3 :memory: < math-forge/data/schema.sql` succeeds
  - **Verify**: `sqlite3 /tmp/test_mf.db < math-forge/data/schema.sql && sqlite3 /tmp/test_mf.db "PRAGMA integrity_check; SELECT COUNT(*) FROM domains;" && rm /tmp/test_mf.db`
  - **Commit**: `feat(database): add knowledge.db schema with FTS5`

- [x] 1.4 Create .gitignore and bootstrap script
  - **Do**: Create `math-forge/.gitignore` (exclude data/*.db, *.pyc, __pycache__/). Create `math-forge/scripts/bootstrap.sh` that creates knowledge.db from schema.sql, runs migration, runs mk stats. chmod +x.
  - **Files**: `math-forge/.gitignore`, `math-forge/scripts/bootstrap.sh`
  - **Done when**: .gitignore excludes DB files, bootstrap.sh is executable
  - **Verify**: `test -x math-forge/scripts/bootstrap.sh && grep -q 'knowledge.db' math-forge/.gitignore`
  - **Commit**: `feat(devops): add .gitignore and bootstrap script`

- [x] 1.5 [VERIFY] Verify database schema creates valid DB with working FTS5
  - **Do**: Create knowledge.db from schema, insert test finding, verify FTS5 MATCH works, verify UPDATE trigger syncs, verify DELETE cleans up
  - **Files**: `math-forge/data/schema.sql` (read-only)
  - **Done when**: FTS5 CRUD cycle passes
  - **Verify**: `sqlite3 /tmp/test_mf.db < math-forge/data/schema.sql && sqlite3 /tmp/test_mf.db "INSERT INTO findings (finding_type, domain_id, title, description, confidence) VALUES ('theorem','nt','test','cubic residue','verified'); SELECT * FROM findings_fts WHERE findings_fts MATCH 'cubic';" && rm /tmp/test_mf.db`
  - **Commit**: (verification only)

## Phase 2: Core Tools (migration + CLI)

- [x] 2.1 Write migration script
  - **Do**: Create `math-forge/scripts/migrate_tracking.py` that migrates from `submissions/tracking.db` to knowledge.db. Read TECH.md "Migration & Bootstrap" section. Must: accept --tracking-db and --knowledge-db args, migrate proven_theorems→findings (type=theorem, confidence=verified), false_lemmas→findings (type=false_lemma, confidence=disproven), failed_approaches→findings (type=failure, confidence=high), candidate_problems→problems table. Use INSERT OR IGNORE. Map domains by keywords. Extract slot numbers from filenames. Print summary. Handle missing tables gracefully.
  - **Files**: `math-forge/scripts/migrate_tracking.py`
  - **Done when**: Script runs on real tracking.db and reports counts
  - **Verify**: `python3 math-forge/scripts/migrate_tracking.py --tracking-db submissions/tracking.db --knowledge-db /tmp/test_migrate.db 2>&1 | grep -q 'Migrated' && rm -f /tmp/test_migrate.db`
  - **Commit**: `feat(migration): add tracking.db to knowledge.db migration script`

- [x] 2.2 Write mk CLI tool — core framework
  - **Do**: Create `math-forge/scripts/mk` as executable bash script. Read TECH.md "KB CLI Tool" and UX.md "Command Design". Reference gpu-forge `kb` at `/tmp/gpu-forge/scripts/kb`. Must have: shebang, set -uo pipefail, 3-level DB resolution (MATH_FORGE_DB > CLAUDE_PLUGIN_ROOT > script-relative), escape_sql(), run_sql(), TTY color detection ([ -t 1 ] && [ -z "${NO_COLOR:-}" ]), error formatting ([math-forge] ERROR: ...), case dispatcher for: search, find, strategies, failed, stats, init, help. mk with no args shows help.
  - **Files**: `math-forge/scripts/mk`
  - **Done when**: `mk help` shows usage, all subcommand stubs exist
  - **Verify**: `chmod +x math-forge/scripts/mk && math-forge/scripts/mk help 2>&1 | grep -q 'search'`
  - **Commit**: `feat(cli): add mk CLI tool framework`

- [x] 2.3 Implement mk search with FTS5
  - **Do**: Add `search` subcommand to mk. Must: accept `mk search <query> [--limit N] [--domain D]`, use FTS5 MATCH with BM25 ranking (weights: title=10, description=5, theorem_statement=5, proof_technique=3, tags=2, why_failed=3), default limit 5, display badges [PROVEN]/[FAILED]/[FALSE], format as `#ID [BADGE] title (problem, slot:N)` with indented description, truncation footer, no-results message.
  - **Files**: `math-forge/scripts/mk`
  - **Done when**: `mk search "test"` returns results or no-results message
  - **Verify**: `math-forge/scripts/mk search "test" 2>&1`
  - **Commit**: `feat(cli): implement mk search with FTS5 BM25`

- [x] 2.4 Implement mk find, strategies, failed, stats
  - **Do**: Add remaining subcommands: `find <problem-id>` (fuzzy match, cross-DB with ATTACH if tracking.db exists, show findings grouped by type + strategies by outcome), `strategies [domain]` (GROUP BY proof_technique, ORDER BY count DESC), `failed [keyword]` (findings where type IN failure/false_lemma, WARNING footer), `stats` (counts by type, by domain, total, newest date).
  - **Files**: `math-forge/scripts/mk`
  - **Done when**: All 4 subcommands produce output
  - **Verify**: `math-forge/scripts/mk stats 2>&1`
  - **Commit**: `feat(cli): implement mk find, strategies, failed, stats`

- [x] 2.5 [VERIFY] Verify migration + CLI end-to-end
  - **Do**: Full pipeline: init DB → migrate real tracking.db → mk search "erdos" → mk stats → mk find "ft_p3"
  - **Files**: (read-only)
  - **Done when**: mk search finds migrated data, mk stats shows non-zero
  - **Verify**: `math-forge/scripts/mk init && python3 math-forge/scripts/migrate_tracking.py && math-forge/scripts/mk stats && math-forge/scripts/mk search "erdos"`
  - **Commit**: (verification only)

## Phase 3: Hooks + Extraction

- [x] 3.1 Write hooks.json configuration
  - **Do**: Create `math-forge/hooks/hooks.json` with SessionStart hook (matcher: startup|resume, timeout: 5, command: context-loader.sh) and PostToolUse hook (matcher: Write|Edit, timeout: 3, command: lean-validator.sh). Use ${CLAUDE_PLUGIN_ROOT} paths.
  - **Files**: `math-forge/hooks/hooks.json`
  - **Done when**: Valid JSON matching Claude Code hooks schema
  - **Verify**: `python3 -c "import json; d=json.load(open('math-forge/hooks/hooks.json')); assert 'SessionStart' in d['hooks']"`
  - **Commit**: `feat(hooks): add hooks.json configuration`

- [x] 3.2 Write SessionStart context-loader hook
  - **Do**: Create `math-forge/hooks/scripts/context-loader.sh`. Read TECH.md "Hook Implementations". Must: resolve DB paths, auto-init knowledge.db if missing, query tracking.db (in-flight count, completed-unfetched, recent proven), query knowledge.db (total findings, recent finding), build ACTION ITEMS, format as plain text with [math-forge] header, output JSON with hookSpecificOutput.additionalContext, inject scripts/ into PATH via CLAUDE_ENV_FILE, complete in <5s, handle missing DBs gracefully.
  - **Files**: `math-forge/hooks/scripts/context-loader.sh`
  - **Done when**: Script exits 0 and outputs valid JSON
  - **Verify**: `chmod +x math-forge/hooks/scripts/context-loader.sh && math-forge/hooks/scripts/context-loader.sh 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print('OK' if 'hookSpecificOutput' in d else 'FAIL')"`
  - **Commit**: `feat(hooks): add SessionStart context-loader hook`

- [x] 3.3 Write PostToolUse lean-validator hook
  - **Do**: Create `math-forge/hooks/scripts/lean-validator.sh`. Must: read JSON from stdin, exit 0 for non-.lean files, detect sorry replacement (old has proof tactics, new has sorry → block with decision:block), detect false lemma references (advisory warning), handle missing jq (grep fallback), complete in <3s, always exit 0 unless blocking.
  - **Files**: `math-forge/hooks/scripts/lean-validator.sh`
  - **Done when**: Blocks sorry replacement, allows non-.lean, warns on false lemmas
  - **Verify**: `chmod +x math-forge/hooks/scripts/lean-validator.sh && echo '{"tool_input":{"file_path":"x.py"}}' | math-forge/hooks/scripts/lean-validator.sh; echo "exit:$?"`
  - **Commit**: `feat(hooks): add PostToolUse lean-validator hook`

- [x] 3.4 Write result extraction pipeline
  - **Do**: Create `math-forge/scripts/extract_findings.py`. Read TECH.md "Result Extraction Pipeline". Must: CLI with `<file.lean> [--slot N] [--problem-id ID] [--db PATH]`, auto-detect slot and problem_id from filename, regex parse declarations/imports/sorry/axioms/tactics, infer domain from imports, generate findings (one per proven theorem, one technique finding for 0-sorry files, one failure for high-sorry), INSERT OR IGNORE into knowledge.db, update problems table, print summary.
  - **Files**: `math-forge/scripts/extract_findings.py`
  - **Done when**: Script extracts findings from a real .lean file
  - **Verify**: `python3 math-forge/scripts/extract_findings.py submissions/nu4_final/slot612_ft_p3_quartic_residue_result.lean --db /tmp/test_ext.db 2>&1 | grep -q 'Extracted' && rm -f /tmp/test_ext.db`
  - **Commit**: `feat(extraction): add .lean result extraction pipeline`

- [x] 3.5 [VERIFY] Verify hooks and extraction work correctly
  - **Do**: Test context-loader JSON output, lean-validator sorry blocking, extraction from slot612 (8 theorems, 0 sorry)
  - **Files**: (read-only)
  - **Done when**: All 3 produce correct output
  - **Verify**: `math-forge/hooks/scripts/context-loader.sh 2>/dev/null | python3 -c "import json,sys; json.load(sys.stdin)" && echo "hooks OK"`
  - **Commit**: (verification only)

## Phase 4: Skills + Commands + Agents

- [x] 4.1 [P] Write skills (number-theory, open-problems, proof-strategies)
  - **Do**: Create 3 skill files in `math-forge/skills/` with YAML frontmatter (name, description with trigger keywords) and body with domain-specific KB query guidance and mk command examples. number-theory.md: NT findings, FT/Erdos/Wolstenholme areas. open-problems.md: KB-informed workflow, PRIME DIRECTIVE, prior knowledge section. proof-strategies.md: technique comparison, cross-domain transfer.
  - **Files**: `math-forge/skills/number-theory.md`, `math-forge/skills/open-problems.md`, `math-forge/skills/proof-strategies.md`
  - **Done when**: All 3 skills have valid frontmatter and mk examples
  - **Verify**: `ls math-forge/skills/*.md | wc -l`
  - **Commit**: `feat(skills): add number-theory, open-problems, proof-strategies skills`

- [x] 4.2 [P] Write slash commands (search, knowledge, stats, failed)
  - **Do**: Create 4 command files in `math-forge/commands/` with YAML frontmatter and step-by-step instructions. search.md: runs mk search, synthesizes. knowledge.md: runs mk find, comprehensive report. stats.md: runs mk stats, dashboard. failed.md: runs mk failed, warns against repeating.
  - **Files**: `math-forge/commands/search.md`, `math-forge/commands/knowledge.md`, `math-forge/commands/stats.md`, `math-forge/commands/failed.md`
  - **Done when**: All 4 commands have valid frontmatter
  - **Verify**: `ls math-forge/commands/*.md | wc -l`
  - **Commit**: `feat(commands): add search, knowledge, stats, failed slash commands`

- [x] 4.3 [P] Write agent configurations
  - **Do**: Create 2 agents in `math-forge/agents/`: investigate.md (sonnet, tools: Read/Grep/Glob/Bash, KB-first progressive disclosure), problem-researcher.md (sonnet, tools: Read/Grep/Glob/Bash/WebSearch, formal-conjectures integration). Both must include "OPEN problems only" directive.
  - **Files**: `math-forge/agents/investigate.md`, `math-forge/agents/problem-researcher.md`
  - **Done when**: Both agents have valid frontmatter with model and tools
  - **Verify**: `ls math-forge/agents/*.md | wc -l`
  - **Commit**: `feat(agents): add investigate and problem-researcher agents`

- [ ] 4.4 [VERIFY] Verify all plugin components present
  - **Do**: Check: plugin.json, schema.sql, mk executable, hooks.json, both hook scripts, 3 skills, 4 commands, 2 agents
  - **Files**: (read-only)
  - **Done when**: All components exist
  - **Verify**: `test -f math-forge/.claude-plugin/plugin.json && test -x math-forge/scripts/mk && test -f math-forge/hooks/hooks.json && echo "All components present"`
  - **Commit**: (verification only)

## Phase 5: Testing + Integration

- [ ] 5.1 Write test helper and fixtures
  - **Do**: Create test infrastructure: `math-forge/tests/test_helper.bash` (PLUGIN_ROOT/MK exports, setup_test_db/teardown_test_db with sample data), `tests/fixtures/sample_proven.lean` (minimal 0-sorry file), `tests/fixtures/sample_failed.lean` (file with 3 sorry).
  - **Files**: `math-forge/tests/test_helper.bash`, `math-forge/tests/fixtures/sample_proven.lean`, `math-forge/tests/fixtures/sample_failed.lean`
  - **Done when**: test_helper sources without errors, fixtures exist
  - **Verify**: `bash -c 'source math-forge/tests/test_helper.bash && echo OK'`
  - **Commit**: `feat(testing): add test helper and fixtures`

- [ ] 5.2 Write BATS tests for mk CLI
  - **Do**: Create 4 BATS test files: test_mk_search.bats (6 cases), test_mk_find.bats (4 cases), test_mk_stats.bats (3 cases), test_mk_utils.bats (3 cases). Each loads test_helper and uses setup/teardown.
  - **Files**: `math-forge/tests/test_mk_search.bats`, `math-forge/tests/test_mk_find.bats`, `math-forge/tests/test_mk_stats.bats`, `math-forge/tests/test_mk_utils.bats`
  - **Done when**: `bats math-forge/tests/test_mk_*.bats` runs
  - **Verify**: `cd math-forge && bats tests/test_mk_search.bats 2>&1 | tail -3`
  - **Commit**: `feat(testing): add mk CLI BATS tests`

- [ ] 5.3 Write hook and golden query tests
  - **Do**: Create: test_session_start_hook.bats (4 cases), test_lean_validator_hook.bats (4 cases), test_golden_queries.bats (8 golden queries for FTS5 relevance regression).
  - **Files**: `math-forge/tests/test_session_start_hook.bats`, `math-forge/tests/test_lean_validator_hook.bats`, `math-forge/tests/test_golden_queries.bats`
  - **Done when**: All test files run
  - **Verify**: `cd math-forge && bats tests/test_golden_queries.bats 2>&1 | tail -3`
  - **Commit**: `feat(testing): add hook tests and golden queries`

- [ ] 5.4 Integrate with existing commands
  - **Do**: Modify existing project commands: add extraction step to /project:fetch and /project:process-result (after audit, call extract_findings.py), add KB query step to /project:sketch (mk search + mk failed before writing), add math-forge section to CLAUDE.md.
  - **Files**: `.claude/commands/fetch.md`, `.claude/commands/sketch.md`, `.claude/commands/process-result.md`, `CLAUDE.md`
  - **Done when**: Commands reference math-forge
  - **Verify**: `grep -l 'math-forge\|extract_findings\|mk search' .claude/commands/*.md CLAUDE.md 2>/dev/null | wc -l`
  - **Commit**: `feat(integration): integrate math-forge with existing commands`

- [ ] 5.5 Run bootstrap and verify full system
  - **Do**: Full bootstrap: create knowledge.db, migrate, verify mk commands, verify hooks, run BATS tests
  - **Files**: (system verification)
  - **Done when**: KB seeded, all mk commands work, tests pass
  - **Verify**: `math-forge/scripts/bootstrap.sh && math-forge/scripts/mk stats && math-forge/scripts/mk search "erdos"`
  - **Commit**: `feat(math-forge): complete plugin v0.1.0`
