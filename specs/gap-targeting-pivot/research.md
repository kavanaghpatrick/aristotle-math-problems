---
spec: gap-targeting-pivot
phase: research
created: 2026-02-17T10:00:00Z
---

# Research: gap-targeting-pivot

## Executive Summary

Full rewrite of project philosophy and tooling to enforce gap-targeting ONLY. Currently the pipeline (11 command skills, 3 math-forge skills, 2 hook scripts, 2 Python pipeline scripts, 2 docs files, 1 mk CLI) contains extensive infrastructure for writing detailed proof strategies in sketches, supporting "known result" tracks, and allowing non-gap submissions. The pivot: strip all proof guidance from sketches (bare conjecture statement only), add hard-block enforcement in the submit pipeline to reject anything not targeting an open gap, and rewrite every skill to embed gap-targeting philosophy with old behaviors removed.

## File Inventory

### Tier 1: Philosophy Documents (rewrite entirely)

| File | Path | Current State | Gap-Targeting Change |
|------|------|---------------|---------------------|
| CLAUDE.md | `/Users/patrickkavanagh/math/CLAUDE.md` | 273 lines. 3-phase pipeline (IDEATE/SKETCH/FORMALIZE). Has Track A-D, case studies, hard rules, decision priority, Lean pitfalls, multi-agent strategy, math-forge section, proof state. Still references Track D "DEPRECATED" but extensively. Sketch section says "50-100 lines" with strategy. | Rewrite top-to-bottom. Remove Tracks B/C/D entirely. Eliminate IDEATE phase (no proof strategy development by us). Sketch becomes "bare conjecture + accumulated context." Remove case studies showing known-result work. Hard rules: only gap-targeting. |
| MEMORY.md | `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` | 98 lines. Prime directive, language rules, core strategy, honest track record, FT p=3 case status, falsified approaches, user directives. | Simplify. Remove detailed track record of known-math formalizations (historical). Strengthen gap-targeting mandate. Remove pipeline details that reference old Tracks. Keep falsified approaches and user directives. |

### Tier 2: Command Skills (rewrite gap-relevant behavior)

| File | Path | Lines | Current Behavior | Gap-Targeting Change |
|------|------|-------|-----------------|---------------------|
| sketch.md | `/Users/patrickkavanagh/math/.claude/commands/sketch.md` | 218 | Full IDEATE+SKETCH: research, classify, computational exploration, falsification check, write 50-100 line sketch with sections (What's Known, Proposed Strategy, Key Lemmas, Main Proof Assembly, Computational Evidence, Mathlib). Has separate templates for OPEN vs KNOWN. | **Major rewrite.** Strip proof strategy sections. New sketch = bare conjecture statement + prior Aristotle results as context files. No "Proposed Strategy", no "Key Lemmas", no proof guidance. Maybe 10-20 lines max. Two-step: (1) identify open gap, (2) state it bare. |
| submit.md | `/Users/patrickkavanagh/math/.claude/commands/submit.md` | 180 | Pre-flight checks (false lemmas, prior attempts), mode detection, queue check, submit, track. No gap-targeting gate. Allows any .txt or .lean. | **Add hard block.** New gate: "Is this submission targeting the open gap of an unsolved problem?" If not, refuse. Check: is the problem open? Is the sketch just the gap statement (not infrastructure/known sub-results)? Pass accumulated context (.lean results from prior slots) via --context. |
| sweep.md | `/Users/patrickkavanagh/math/.claude/commands/sweep.md` | 170 | Full discovery pipeline. Scans formal-conjectures, classifies by openness, assigns Tiers A-D, generates sketches for all Tier A. Still has Track D "Known-Result Formalization" in tier assignments. | **Major rewrite.** Remove Tiers B/C/D. Only Tier A remains: "open gap targeting." Remove computational discovery and falsification tracks (those are separate concerns, not submission tracks). Simplify to: find open problems, state the gap bare, submit. |
| screen.md | `/Users/patrickkavanagh/math/.claude/commands/screen.md` | 103 | Quick assessment. "Default: ACCEPT." Tracks A/B/C/D recommendation. DB checks. | **Simplify.** Only question: "Is this an open problem?" If yes, ACCEPT. If not, SKIP. Remove scoring, remove track assignment. |
| screen-batch.md | `/Users/patrickkavanagh/math/.claude/commands/screen-batch.md` | 81 | Batch screen. Tiers A/B/C/D/X classification. AMS tag mapping, finite structure signals. | **Simplify.** Binary: OPEN (submit bare gap) vs SKIP (not open). Remove tier system. |
| fetch.md | `/Users/patrickkavanagh/math/.claude/commands/fetch.md` | 81 | Fetch results, deep audit, extract knowledge. | **Add gap-targeting assessment to audit.** When fetching: did the result resolve the open gap, or did it just compile infrastructure? Tag results honestly with target_resolved. |
| audit.md | `/Users/patrickkavanagh/math/.claude/commands/audit.md` | 125 | 8-point audit (sorry, axiom, self-loops, sym2, cover defs, false lemmas, structure, novelty). Novelty assessment: FIRST-EVER/EXTENSION/RE-PROOF/INFRASTRUCTURE. | **Reframe novelty assessment.** Replace with gap-resolution assessment: did this resolve/advance the OPEN GAP? Not "first-ever formalization" (that's still known math). |
| process-result.md | `/Users/patrickkavanagh/math/.claude/commands/process-result.md` | 115 | Extract metrics, run audit, determine verdict, update DB, extract knowledge. | **Add target_resolved assessment.** When processing: does the result contain a proof of the actual open conjecture (not just sub-lemmas)? Set target_resolved=1 only if yes. |
| optimize.md | `/Users/patrickkavanagh/math/.claude/commands/optimize.md` | 108 | Recommends pipeline path (INFORMAL vs FORMAL). Tactic analysis. | **Simplify.** Only recommendation: "State the gap bare, submit INFORMAL." Remove FORMAL paths entirely (gap-targeting is always INFORMAL). |
| debate.md | `/Users/patrickkavanagh/math/.claude/commands/debate.md` | 97 | Multi-AI debate with context accumulation. | **Minimal change.** Debates are fine for gap understanding. Add: debates should identify the EXACT open gap, not develop proof strategies. |
| status.md | `/Users/patrickkavanagh/math/.claude/commands/status.md` | 21 | Check Aristotle job status. | **No change needed.** Pure status check. |

### Tier 3: Math-Forge Skills (rewrite philosophy)

| File | Path | Lines | Current Behavior | Gap-Targeting Change |
|------|------|-------|-----------------|---------------------|
| open-problems.md | `/Users/patrickkavanagh/math/math-forge/skills/open-problems.md` | 47 | KB-informed sketch writing. Queries prior knowledge, builds "Prior Knowledge" section for sketches, proposes NEW approaches. | **Rewrite.** Remove "propose NEW approach" step. Instead: query KB for prior Aristotle results on this problem, pass those as context files. No proof strategy in sketch. |
| number-theory.md | `/Users/patrickkavanagh/math/math-forge/skills/number-theory.md` | 45 | NT-specific KB queries: search, find, failed, strategies. | **Minor rewrite.** Keep KB queries (they prevent repeat failures). Remove "proven techniques" focus -- we don't guide Aristotle's technique choice. |
| proof-strategies.md | `/Users/patrickkavanagh/math/math-forge/skills/proof-strategies.md` | 48 | Strategy comparison and cross-domain technique transfer. | **Remove or gut.** Proof strategy selection is exactly what we're eliminating. We don't choose strategies; Aristotle does. Convert to "prior results" skill that just surfaces what Aristotle has already tried. |

### Tier 4: Hook Scripts (add enforcement)

| File | Path | Lines | Current Behavior | Gap-Targeting Change |
|------|------|-------|-----------------|---------------------|
| lean-validator.sh | `/Users/patrickkavanagh/math/math-forge/hooks/scripts/lean-validator.sh` | 87 | PostToolUse hook. Blocks sorry replacement in .lean files, warns on false lemma references. | **Add gap-targeting check.** When writing a .txt sketch: warn if the sketch contains proof strategy keywords (e.g., "Proof:", "Lemma:", "Strategy:", "by induction", "using CRT"). The sketch should be bare. |
| context-loader.sh | `/Users/patrickkavanagh/math/math-forge/hooks/scripts/context-loader.sh` | 118 | SessionStart hook. Generates briefing with queue status, unfetched results, near-misses, action items. | **Add gap-targeting reminder.** Inject "REMINDER: Gap-targeting only. Bare conjecture statements. No proof guidance." into every session briefing. |
| hooks.json | `/Users/patrickkavanagh/math/math-forge/hooks/hooks.json` | 28 | Registers SessionStart and PostToolUse hooks. | **Possibly add new hook.** Could add a pre-submit hook that validates sketches are gap-targeting (though the submit.md skill gate may suffice). |

### Tier 5: Pipeline Scripts (add hard gate)

| File | Path | Lines | Current Behavior | Gap-Targeting Change |
|------|------|-------|-----------------|---------------------|
| safe_aristotle_submit.py | `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` | 462 | Safety checks: lockfile, duplicate detection, rate limit, queue capacity, file validation. No content-level validation. | **Add gap-targeting gate.** New check: for .txt files, validate the sketch is gap-targeting (not infrastructure). Heuristic: reject if >50 lines, reject if contains "Proof Strategy" or "Key Lemmas" sections. For .lean files: reject (gap-targeting is always INFORMAL .txt). This is the HARD BLOCK. |
| aristotle_fetch.py | `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` | 483 | Fetch results, audit (sorry/axiom/negation), update DB. Uses verdict: compiled_clean/disproven/near_miss/completed/failed. | **Add target_resolved assessment.** After audit: classify whether the result actually resolved the open gap. Currently sets `target_resolved=0` always -- needs intelligent classification. |
| extract_findings.py | `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` | 384 | Parses .lean results into knowledge.db findings. Extracts declarations, imports, tactics, generates findings per theorem. | **Add gap-resolution finding type.** New finding_type: 'gap_progress' for results that advance the open gap (vs 'theorem' which just means "compiled clean"). |

### Tier 6: Database Schema (add columns/types)

| File | Path | Current State | Gap-Targeting Change |
|------|------|---------------|---------------------|
| tracking.db schema | `/Users/patrickkavanagh/math/submissions/tracking.db` | submissions table has `target_resolved INTEGER DEFAULT 0`. No gap-targeting fields. | **Add fields.** `gap_statement TEXT` (the exact open gap being targeted), `submission_type TEXT CHECK(...)` (gap_targeting/infrastructure/falsification). Migration needed. |
| knowledge.db schema | `/Users/patrickkavanagh/math/math-forge/data/schema.sql` | findings table has finding_type IN ('theorem','technique','failure','false_lemma','computation','mathlib_api','insight'). | **Add finding_type 'gap_progress'.** Also add to findings: `targets_open_gap INTEGER DEFAULT 0`, `gap_id TEXT` (linking to which open gap). |

### Tier 7: mk CLI (add gap-targeting commands)

| File | Path | Lines | Current Behavior | Gap-Targeting Change |
|------|------|-------|-----------------|---------------------|
| mk | `/Users/patrickkavanagh/math/math-forge/scripts/mk` | 411 | Commands: search, find, strategies, failed, stats, init, submit, status, partials, resubmittable, query. | **Add `mk gaps` command.** Lists all open problems being targeted with their gap statements and prior Aristotle results. Also: `mk context <problem>` to gather all prior .lean results for passing as context to new submissions. |

### Tier 8: Settings / Plugin Config (no change)

| File | Path | Change |
|------|------|--------|
| settings.json | `/Users/patrickkavanagh/math/.claude/settings.json` | No change needed. |
| plugin.json | `/Users/patrickkavanagh/math/math-forge/.claude-plugin/plugin.json` | No change needed. |

## Current Sketch Format vs. Gap-Targeting Format

### Current (slot662 example - 66 lines):
```
Erdos Problem 11: ...
=== FORMAL STATEMENT ===
theorem erdos_11 (n : N) ...
=== PROOF STRATEGY ===
APPROACH 1: Sieve-theoretic density argument
[30 lines of detailed mathematical reasoning]
APPROACH 2: Elementary bounded verification
[10 lines]
APPROACH 3: Conditional on abc-conjecture
[5 lines]
=== WHAT TO PROVE ===
PRIMARY: ...
FALLBACK 1-4: ...
```

### Gap-Targeting (proposed - ~10 lines):
```
OPEN GAP: Erdos Problem 11
Every odd n > 1 is the sum of a squarefree number and a power of 2.

theorem erdos_11 (n : N) (hn : Odd n) (hn' : 1 < n) :
    exists k l : N, Squarefree k and n = k + 2 ^ l

Status: OPEN. Computationally verified to n < 2^50.
```
Plus: `--context slot662_result.lean slot667_result.lean` (prior Aristotle attempts).

The fundamental shift: WE provide the bare gap, Aristotle provides the proof. No strategy, no lemmas, no guidance from us.

## Technical Constraints

### Hard Constraints
1. **aristotlelib API**: `prove_from_file()` accepts `input_file_path`, `project_input_type` (INFORMAL/FORMAL_LEAN), `context_file_paths`. Context files are the mechanism for passing prior results. No other parameters available.
2. **Queue limit**: 5 concurrent Aristotle jobs. Unchanged by this rewrite.
3. **sqlite3 ALTER TABLE**: Can add columns, cannot modify CHECK constraints without table recreation. knowledge.db finding_type CHECK constraint needs table recreation or a separate migration.
4. **BATS tests**: 32 existing tests in `math-forge/tests/`. Changes to mk CLI, hooks, and extract_findings.py must not break these.
5. **Active submissions**: Any in-flight Aristotle jobs (slot646-650+) must not be disrupted. The rewrite is about FUTURE submissions.

### Soft Constraints
1. **Sketch validation heuristic**: Detecting "is this just a bare gap statement?" is imperfect. A line-count threshold (>30 lines = too much guidance?) plus keyword detection ("Proof Strategy", "Key Lemma") is a reasonable heuristic but will have false positives/negatives.
2. **target_resolved classification**: Determining whether a result "resolved the open gap" requires understanding what the gap is. This is a human judgment call; automation is approximate at best.
3. **Context file accumulation**: Need a clean way to gather all prior .lean results for a problem to pass as --context. Currently no automated mapping from problem_id to result files.

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Breaking existing submissions in flight | HIGH | Only apply new rules to future submissions. Keep old commands working for fetching/processing existing results. |
| BATS test failures | MEDIUM | Run `bats math-forge/tests/` after each change. Tests cover mk search/find/stats, lean-validator, session-start. |
| Sketch validation false positives | MEDIUM | Make the hard block in safe_aristotle_submit.py have a --force-gap override (user can explicitly bypass). But per user directive: "No overrides." |
| Losing useful context in sketches | LOW | Prior Aristotle results passed as --context provide all the context needed. The KB (mk search, mk failed) prevents repeat failures. |
| Over-simplification killing submissions | LOW | Aristotle's 100% INFORMAL success rate suggests it doesn't need our proof strategies. The bare-gap format may actually work BETTER since it doesn't constrain Aristotle's search. |
| knowledge.db schema migration | LOW | Adding a new finding_type to CHECK constraint requires table recreation. Standard SQLite pattern: create new table, copy data, drop old, rename. |

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | HIGH | All changes are to text files (skills), Python scripts, and bash scripts. No complex dependencies. |
| Effort Estimate | L (Large) | 22+ files to modify. Philosophy rewrite of 2 docs, 10 command skills, 3 math-forge skills, 2 hooks, 2 pipeline scripts, 1 CLI, 2 schemas. But most changes are text rewrites, not complex code. |
| Risk Level | MEDIUM | Main risk is breaking BATS tests and disrupting in-flight submissions. Mitigated by incremental rollout. |

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| honest-tooling | Medium | false | Overlapping files (mk CLI, safe_aristotle_submit.py, aristotle_fetch.py). Already completed most tasks. honest-tooling changed "proven" to "compiled_clean" -- gap-targeting adds further status distinctions. No conflict: honest-tooling is about labeling, gap-targeting is about submission gating. |
| math-forge | Medium | false | Overlapping files (all math-forge skills, hooks, mk CLI, extract_findings.py). math-forge spec was about "wiring KB into pipeline" -- gap-targeting changes WHAT the pipeline does, not the KB plumbing. No conflict but will modify some of the same files. |

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| BATS tests | `bats math-forge/tests/` | math-forge/tests/*.bats |
| Lint | Not found | No package.json, no Makefile |
| TypeCheck | Not found | Python scripts have no type-checking setup |
| Build | Not found | No build step |
| Unit Test | `bats math-forge/tests/` | Only automated tests available |

**Local CI**: `bats math-forge/tests/`

No package.json, Makefile, or CI configs exist in this project.

## Recommendations for Requirements

1. **Phase the rollout**: Start with docs (CLAUDE.md, MEMORY.md), then skills, then pipeline scripts, then schema changes. Each phase is independently valuable and testable.

2. **The "hard block" in safe_aristotle_submit.py**: Implement as a new function `check_gap_targeting(input_file)` that:
   - For .txt files: reject if >50 lines OR contains "Proof Strategy"/"Key Lemma"/"APPROACH" sections
   - For .lean files: reject entirely (gap-targeting = INFORMAL only)
   - Return clear error message explaining why
   - NO --force override (per user directive)

3. **Context accumulation**: Add `mk context <problem_id>` command to mk CLI that:
   - Queries tracking.db for all prior submissions for a problem
   - Finds corresponding _result.lean files
   - Outputs paths suitable for `--context` flag

4. **Sketch template**: Replace the current 50-100 line template with a minimal template:
   ```
   OPEN GAP: [problem name]
   [1-3 sentence statement of the unsolved conjecture]
   [Formal statement in Lean syntax if available]
   Status: OPEN. [Brief note on what's known, e.g., "verified to N=10^5"]
   ```

5. **target_resolved tracking**: The existing `target_resolved INTEGER DEFAULT 0` column in submissions is sufficient. Set it manually when reviewing results (human judgment needed for "did this resolve the open gap?").

6. **Schema changes**: Add `gap_statement TEXT` and `submission_type TEXT` to tracking.db submissions table. Add `targets_open_gap INTEGER DEFAULT 0` to knowledge.db findings table. These are non-breaking ALTERs.

7. **BATS test updates**: Any tests that validate sketch format or submission behavior will need updating. Run `bats math-forge/tests/` as quality gate after each file change.

8. **Keep fetch/process-result/status largely unchanged**: These are observation tools, not submission tools. The gap-targeting enforcement is at the SUBMIT gate, not the fetch/audit gate.

## Open Questions

1. **How strict should sketch length enforcement be?** The user said "bare conjecture statement + zero proof guidance." Should we literally block anything over 10 lines? 20? 30? Or just block known-bad patterns (strategy sections)?

2. **What about falsification submissions?** Currently Track C submits negations to disprove conjectures. Is falsification still allowed under gap-targeting? It targets "is the gap real?" rather than "closing the gap." Suggest: allow falsification as a special case with explicit `--falsify` flag.

3. **What about bounded verification?** Currently Track B uses native_decide for bounded cases. Under gap-targeting: is "prove for n < 10000" gap-targeting or infrastructure? Suggest: only if the bounded case IS the open gap (rare).

4. **Should prior Aristotle results be passed automatically?** The user said "allow accumulated context." Should `mk submit` auto-detect and attach prior results, or require explicit `--context` specification?

5. **What constitutes "targeting an open gap"?** Is proving a sub-case of an open conjecture (e.g., "Grimm's conjecture for k=3") gap-targeting? The user said "only the open gap itself." Strict interpretation: the sketch must state the FULL conjecture, not a sub-case.

## Sources
- `/Users/patrickkavanagh/math/CLAUDE.md` (project philosophy, 273 lines)
- `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` (memory, 98 lines)
- `/Users/patrickkavanagh/math/.claude/commands/*.md` (11 command skills)
- `/Users/patrickkavanagh/math/math-forge/skills/*.md` (3 math-forge skills)
- `/Users/patrickkavanagh/math/math-forge/hooks/scripts/*.sh` (2 hooks)
- `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` (462 lines)
- `/Users/patrickkavanagh/math/scripts/aristotle_fetch.py` (483 lines)
- `/Users/patrickkavanagh/math/math-forge/scripts/extract_findings.py` (384 lines)
- `/Users/patrickkavanagh/math/math-forge/scripts/mk` (411 lines)
- `/Users/patrickkavanagh/math/math-forge/data/schema.sql` (knowledge.db schema)
- `/Users/patrickkavanagh/math/submissions/tracking.db` (tracking.db schema via .schema)
- `/Users/patrickkavanagh/math/submissions/sketches/slot662_erdos11_squarefree_pow2.txt` (current sketch example, 66 lines)
- `/Users/patrickkavanagh/math/submissions/sketches/slot670_erdos375_grimm.txt` (current sketch example, 68 lines)
- `/Users/patrickkavanagh/math/specs/honest-tooling/.progress.md` (related spec)
- `/Users/patrickkavanagh/math/specs/math-forge/.progress.md` (related spec)
