# Infrastructure Changes — May 30 2026

**Synthesized by:** I5 (agent 5 of 10)
**Status:** Active rollout. Some I-agent outputs may be in-flight; placeholders marked `[PENDING]`.
**Context:** F-team audit (F1-F10) + W-team research (W1-W8) surfaced systemic gaps; the I-team (I1-I10) executes the fix.

---

## TL;DR

The pre-May-30 architecture was **bare-gap-only**: every submission was a ≤30-line .txt with the formal MCGS subsystem as the only entry point. F1 found 57% of `compiled_advance` rows were brute-force bounded extensions; F2 found 0/220 sketches had cross-domain literature attached and the auto-context query was silently broken; W8 found we had never used Aristotle's informal-reasoner subsystem.

The post-May-30 architecture is a **four-lane pipeline** (bare / closure / fusion / informal) with:
- a working auto-context query (I1)
- five new audit columns + a `submissions_audit` view (I2)
- ex-ante `mathematical_content_score` to detect brute-force masquerading as advance
- routed strategy work into `.fusion.json` companions (rather than throwaway chat)
- explicit invocation of Aristotle subsystem #2 via `--informal-mode`

---

## Agent-by-agent

### I1 — `gather_context()` query rewrite

**File:** `docs/infrastructure_changes_may30/I1_gather_context_fix.md`
**Status:** LANDED

**Root cause:** The auto-context query in `scripts/safe_aristotle_submit.py::gather_context()` filtered on `status IN ('compiled_clean', 'near_miss', 'completed')`. None of those values exist in the current schema — the canonical statuses are `submitted / compile_failed / compiled_partial / compiled_no_advance / compiled_advance / disproven`. The intersection was the empty set; the query returned 0 rows on every call.

**Blast radius:** 407 of 410 submissions made AFTER ≥1 prior artifact existed received empty auto-context. 94 submissions across 7 key problem_ids (feit_thompson 11, tuza_nu4 69, leinster 10, etc.) silently lost context.

**Fix:**
- Replaced status-enum filter with artifact-based filter (`output_file IS NOT NULL AND output_file != ''`); excludes only `compile_failed`.
- Honors the `verified` column when present (rows with `verified=0` are audit-rejected and excluded).
- Added a canary warning when 0 artifacts attach despite >0 prior submissions exist for the problem_id.
- Added missing-file warning for paths that no longer exist on disk (e.g., old `~/Downloads/` paths).
- Threaded `--verbose-context` CLI flag for diagnostics.
- 10 tests in `tests/test_gather_context.py` — all passing.

### I2 — Schema unification

**File:** `docs/infrastructure_changes_may30/I2_schema_unification.md`
**Status:** LANDED

**Changes:**
- Added 5 columns to `submissions`: `lane`, `mathematical_content_score`, `fusion_json`, `informal_mode_used`, `paired_llm`.
- Backfilled `lane='bare'` on all 1166 prior rows (factually correct for the pre-lane era).
- F1 verdict backfill: slot720 mcs=5, slot722 mcs=3 (slots 736-739 not yet in DB but tolerated by the migration).
- Created `submissions_audit` view exposing every audit axis in stable column order.
- Added `--fusion-lane`, `--informal-mode`, `--paired-llm <name>` CLI flags to `safe_aristotle_submit.py`.
- Lane resolution precedence: `informal-mode` > `fusion-lane` > `real_closure_candidate=true` > default `bare`.
- Migration is idempotent; rollback procedure documented.

### I3 — Skill audit `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I3_skill_audit.md` (not yet landed at synthesis time)
**Expected scope:** Audit of plugin skills referenced in CLAUDE.md commands (`/sketch`, `/submit`, `/fetch`, `/process-result`, etc.); identify which skills need updating to support the 4-lane pipeline; reconcile with `mathematical_content_score` audit step.

### I4 — Literature check pipeline `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I4_literature_check.md` (not yet landed at synthesis time)
**Expected scope:** Implement the F2 finding's literature-check hard rule. Build/extend the auto-context attachment so that every `structural-open` target gets ≤2-year cross-domain literature attached. Likely changes: `gather_context()` extension or a new helper; integration with `mk context`.

### I5 — Documentation unification (THIS DOC)

**Files updated:**
- `/Users/patrickkavanagh/math/CLAUDE.md` (4-lane pipeline; Aristotle System Facts; Hard Rules extended; Status Enum canonical; new DB columns; decision tree)
- `/Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` (directive #5 added; ARISTOTLE FACTS section; LITERATURE-CHECK section; falsified approaches updated)
- `/Users/patrickkavanagh/math/docs/feasibility_filter_rubric.md` (v1.1 addendum: `mathematical_content_score`, `paired_llm`, 4-lane decision criteria)
- `/Users/patrickkavanagh/math/docs/aristotle_usage_guide.md` (NEW: provenance, 3 subsystems, 4 lanes, success patterns, failure modes, calibration)
- `/Users/patrickkavanagh/math/docs/infrastructure_changes_may30/CHANGELOG.md` (this file)

### I6 — `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I6_*.md` (not yet landed at synthesis time)

### I7 — `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I7_*.md` (not yet landed at synthesis time)

### I8 — `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I8_*.md` (not yet landed at synthesis time)

### I9 — `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I9_*.md` (not yet landed at synthesis time)

### I10 — `[PENDING]`

**File:** `docs/infrastructure_changes_may30/I10_*.md` (not yet landed at synthesis time)

---

## Pre/post architecture

### Pre-May-30 (bare-gap-only, broken auto-context, no closure axis enforced)

```
                           ┌────────────────────────────┐
                           │  User: "submit problem X"  │
                           └─────────────┬──────────────┘
                                         │
                                         v
                ┌─────────────────────────────────────────────┐
                │ /sketch -> bare ≤30-line .txt (BARE only)   │
                │  - no companion file                        │
                │  - no literature attached (F2: 0/220)       │
                │  - no closure-axis classification           │
                └─────────────────────┬───────────────────────┘
                                      │
                                      v
                ┌─────────────────────────────────────────────┐
                │ check_gap_targeting()  [WORKING]            │
                │ gather_context()       [SILENTLY BROKEN]    │
                │   - returns 0 rows on every call (I1)       │
                │   - 407/410 post-artifact subs got nothing  │
                └─────────────────────┬───────────────────────┘
                                      │
                                      v
                ┌─────────────────────────────────────────────┐
                │ Aristotle MCGS subsystem (formalizer only)  │
                │   - subsystem #1 of 3 (W-team finding)      │
                │   - informal reasoner: never invoked        │
                │   - geometry solver: not applicable         │
                └─────────────────────┬───────────────────────┘
                                      │
                                      v
                ┌─────────────────────────────────────────────┐
                │ Audit: status set (5-status enum)           │
                │   - 57% of "compiled_advance" were          │
                │     brute-force bounded ext (F1)            │
                │   - no ex-ante content score                │
                └─────────────────────────────────────────────┘
```

### Post-May-30 (4 lanes, working auto-context, schema unified)

```
                           ┌────────────────────────────┐
                           │  User: "submit problem X"  │
                           └─────────────┬──────────────┘
                                         │
                                         v
        ┌───────────────────────────────────────────────────────────┐
        │ Lane selection:                                           │
        │   --informal-mode  → INFORMAL  (lane='informal')          │
        │   --fusion-lane    → FUSION    (lane='fusion')            │
        │   .closure.json    → CLOSURE   (lane='closure' if         │
        │                                  real_closure_candidate=  │
        │                                  true)                    │
        │   (default)        → BARE      (lane='bare')              │
        └───────────────────────┬───────────────────────────────────┘
                                │
                                v
        ┌───────────────────────────────────────────────────────────┐
        │ Gates (in order):                                         │
        │  check_gap_targeting()  [WORKING]                         │
        │  check_closure_axis()   [enforced for CLOSURE; warn else] │
        │  literature_check       [F2 fix; ≤2-year for struct-open] │
        │  gather_context()       [FIXED I1: artifact-based filter] │
        └───────────────────────┬───────────────────────────────────┘
                                │
                                v
        ┌───────────────────────────────────────────────────────────┐
        │ Aristotle subsystems (lane-routed):                       │
        │   BARE     → MCGS                                         │
        │   CLOSURE  → MCGS                                         │
        │   FUSION   → MCGS + .fusion.json dossier as context       │
        │   INFORMAL → informal reasoner FIRST, then MCGS           │
        └───────────────────────┬───────────────────────────────────┘
                                │
                                v
        ┌───────────────────────────────────────────────────────────┐
        │ Audit (5-status enum + new columns):                      │
        │   lane, paired_llm, informal_mode_used, fusion_json       │
        │   closure_axis_json, mathematical_content_score (0-10)    │
        │   submissions_audit view exposes all axes                 │
        └───────────────────────────────────────────────────────────┘
```

---

## Migration checklist

For operators wanting to adopt the new architecture in an existing checkout:

- [x] Pull latest `main` branch (or feat/math-forge per current branch).
- [x] Run `python3 scripts/migrate_add_lane_columns_may30.py` (idempotent).
- [x] Verify `submissions_audit` view exists: `sqlite3 submissions/tracking.db ".schema submissions_audit"`.
- [x] Verify column count = 47: `sqlite3 submissions/tracking.db ".schema submissions" | wc -l`.
- [x] `tests/test_gather_context.py` runs clean: `pytest tests/test_gather_context.py -v`.
- [ ] Review prior `compiled_advance` rows; populate `mathematical_content_score` honestly (audit phase, ongoing).
- [ ] For any NEW submissions to a problem with prior context: pass `--verbose-context` once to verify auto-context is attaching artifacts.
- [ ] For FUSION-lane usage: see I3 / I6 skill outputs once they land for the `.fusion.json` schema.
- [ ] For INFORMAL-lane usage: workflow is the E124 / E481 pattern — bare problem statement, no Lean scaffold required.

---

## Known issues

1. **I3 / I4 / I6-I10 still PENDING at I5 synthesis time.** This CHANGELOG will need a follow-up edit when those land. The skill audit (I3) will likely require updates to `/sketch`, `/submit`, `/fetch` commands; the literature-check pipeline (I4) will likely require schema additions or a new helper.

2. **`.fusion.json` schema is provisional.** I5's `aristotle_usage_guide.md` lists fields (paired_llm, strategy_outline, key_lemmas, cross_domain_literature, airlock_status, rationale) but the canonical schema lives in a sibling I-agent output that has not landed yet.

3. **Slots 736-739 (May 30 batch) are not in the DB.** I2's F1 backfill reported `MISS (slot not in DB)` for these. When they land via a future fetch/submit cycle, re-running `migrate_add_lane_columns_may30.py` will backfill their scores.

4. **leinster + erdos_647 auto-context is empty post-I1 fix.** leinster has 9 artifact rows but ALL are `verified=0` (audit-rejected). erdos_647 has 1 artifact row but its file is missing on disk. Both correctly result in `0 artifacts attached` with a canary warning. Operators should know these are correct behaviors, not bugs.

5. **`mathematical_content_score` is audit-populated, not drafter-populated for legacy rows.** Only 2 of 1166 rows have it set so far (slot720=5, slot722=3). Backfilling the other 1164 requires a multi-day audit pass; this is documented in `feasibility_filter_rubric.md` v1.1 but not yet executed.

6. **Closure-axis gate is in WARN-only transition for missing companions.** New sketches drafted after 2026-05-30 should ship `.closure.json` unconditionally; the gate will eventually move from WARN to REJECT for missing companions.

7. **W8 (informal-mode usage) is a forward bet, not a delivered fact.** The INFORMAL lane is wired up in the schema (I2) and described in docs (I5), but we have not yet executed an INFORMAL-mode submission. First trial expected next batch.

---

## Authority

- F-team audit (F1-F10): `analysis/` directory, may30 files
- W-team research (W1-W8): `analysis/web_research_aristotle_*.md`, `analysis/web_research_academic_papers.md`, `analysis/web_research_synthesis.md`
- I-team docs: `docs/infrastructure_changes_may30/I*_*.md`
- This CHANGELOG: I5, May 30 2026; updates as sibling outputs land.
