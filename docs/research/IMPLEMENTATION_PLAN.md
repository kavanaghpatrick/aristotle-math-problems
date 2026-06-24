# IMPLEMENTATION_PLAN.md

## ⚡ Pilot finding 2026-05-28 — re-ranking

**PILOT_ERDOS850 (3 arms) revealed a structural bug that outranks every prior recommendation:** the bare-conjecture template `(P) ∨ ¬ (P)` is the law of excluded middle. Aristotle discharges it with `exact em _` in one line. All 3 pilot arms (bare control, Claude sketch-first, bare-then-ask) returned identical em-tautology proofs. The sketch arm provided no benefit because the goal was already trivially decidable.

**Implications for the proposals below:**

- ✅ **Proposal #2 (schema honesty)** — SHIPPED. Pilot vindicated this completely; without `axiom_count` and the collapsed status vocab the 3 em-tautology results would have looked like "compiled_clean" wins. See `scripts/migrations/2026_05_28_schema_honesty.sql`.
- 🚀 **Proposal #1 (informal sketches)** — DEFERRED for the bottleneck reason. The pilot showed sketches CANNOT help when the theorem statement is structurally a tautology. The fix is at the statement level, not the method level. Sketches may still help — we just can't measure that until the statement-template bug is fixed.
- 🆕 **NEW Proposal #0 (em-tautology gate)** — SHIPPED. `safe_aristotle_submit.py` now rejects `P∨¬P` patterns at submit time; `audit_proven.py` flags them in existing files. This is the new highest-impact-per-cost change. See `_looks_like_em_tautology()` and the CRITICAL audit check.
- 🔁 **Pilot re-run** — proposed: same 3-arm structure on `erdos850_existence.txt` (existence form, NOT the disjunction). Slots 720/721/722 pending user go-ahead.

See `docs/research/PILOT_ERDOS850.md` for full pilot results and remediation.

---

Concrete plan for the **TOP 2** proposals from `improvement_proposals.md`, refined by a 3-round multi-AI `/debate` (Codex/GPT-5.2 was the substantive voice; Grok and Gemini transports failed). **Nothing in this document is applied yet** — approval-gated.

- **#2** (no-conflict quick win, ship first) — make the `submissions` schema honest. Now also adds provenance columns for #1.
- **#1** (highest impact, conflicts with PRIME DIRECTIVE) — replace bare-conjecture doctrine with informal-sketch stage. Conflict is the first open question.
- **PILOT** (new section) — 9-submission 3×3 experiment Codex's debate output recommends before scaling sketches to default.

**Key debate refinements over the original draft:**
1. Sketches are required for *serious* gap-targeting, NOT mandatory for every submission — bare stays as a measurable control arm for falsification, baselines, and ablations.
2. Hybrid model design: Gemini 3 Deep Think AND GPT-5.5 Pro both generate sketches; Codex merges/audits into one bounded submission. Avoids premature single-model commitment.
3. Provenance tracking is mandatory — without it, sketch results can't be attributed to a source.
4. No scaling sketches to default until either 1 `target_resolved=1` OR repeated `compiled_advance` without axiom theater shows up in the pilot.

**Model versions (updated May 28, 2026 after user flagged staleness):**
- **GPT-5.5 Pro** (released Apr 23, 2026) replaces the earlier GPT-5.2 Pro reference in the research docs. FrontierMath Tier 4: 39.6% vs 31% (GPT-5.2 Pro) vs 16.7% (Gemini 3.1 Pro). 1M context. Already helped discover a Lean-verified Ramsey-number proof.
- **Gemini 3 Deep Think** replaces the plain Gemini 3.1 Pro reference. Separate product line from the Pro tier; received a major upgrade May 2026 explicitly built "in close partnership with scientists and researchers to tackle tough research challenges." New SOTA: 48.4% on Humanity's Last Exam (no tools), 84.6% on ARC-AGI-2 (verified), 3455 Elo on Codeforces, IMO 2025 gold-medal. **Access caveat**: Deep Think is gated — Google AI Ultra subscription for app access; early-access only via the Gemini API. Standard Gemini 3.1 Pro is the fallback (1M context, still the strongest *generally available* reasoning model). 3.5 Flash isn't for reasoning; 3.5 Pro delayed to June 2026.
- **Codex CLI** likely already uses GPT-5.3-Codex (released spring 2026 — first model fusing Codex + GPT-5 training stacks). Verify with `codex --version` before pilot.

---

## Proposal #2 — schema honesty (no-conflict)

### Why first
We can't measure #1 without it. Verified via `sqlite3 tracking.db`: 0/1,157 `target_resolved=1`, 25 distinct `status` values, 38/1,157 `contribution_statement`, 0/1,157 `execution_seconds`, 751/1,157 `verified` NULL.

### A. SQL migration

**New file: `scripts/migrations/2026_05_28_schema_honesty.sql`** (~90 lines)

```sql
BEGIN;
-- Honesty columns
ALTER TABLE submissions ADD COLUMN axiomatizes_prior_work INTEGER DEFAULT 0;
ALTER TABLE submissions ADD COLUMN axiom_count INTEGER DEFAULT 0;
ALTER TABLE submissions ADD COLUMN cost_usd REAL;
ALTER TABLE submissions ADD COLUMN execution_seconds REAL;  -- currently 0/1157 populated

-- Sketch provenance (required by #1 — set when pattern='informal_sketch_v1')
ALTER TABLE submissions ADD COLUMN sketch_model_primary TEXT;
ALTER TABLE submissions ADD COLUMN sketch_model_secondary TEXT;
ALTER TABLE submissions ADD COLUMN sketch_hash TEXT;
ALTER TABLE submissions ADD COLUMN candidate_lemmas_json TEXT;
ALTER TABLE submissions ADD COLUMN prior_context_used TEXT;
ALTER TABLE submissions ADD COLUMN experiment_arm TEXT;   -- 'bare' | 'sketch_first' | 'bare_then_ask' | NULL

-- Status v2 collapse
ALTER TABLE submissions ADD COLUMN status_v2 TEXT;
UPDATE submissions SET status_v2 = CASE
  WHEN status IN ('submitted','queued','running','in_progress','pending','draft','ready') THEN 'submitted'
  WHEN status IN ('failed','error','broken','invalid','timeout','tainted','missing','stale') THEN 'compile_failed'
  WHEN status IN ('partial','incomplete','near_miss') THEN 'compiled_partial'
  WHEN status IN ('completed','compiled_clean','historical','known_result','review_complete') THEN 'compiled_no_advance'
  WHEN status IN ('disproven','disproved','likely_false') THEN 'disproven'
  ELSE 'compile_failed' END;
COMMIT;
-- compiled_advance is opt-in: requires contribution_statement NOT NULL AND
-- axiomatizes_prior_work = 0 AND target_resolved = 1. Set only by /audit.
```

A short Python runner (`scripts/migrations/run.py`, ~40 lines) backs up the DB, applies the SQL, swaps `status_v2`→`status`, prints before/after counts.

### B. `scripts/audit_proven.py` change (~10 new lines)

```python
axiom_count = sum(1 for l in lean_text.splitlines()
                  if re.match(r'^\s*axiom\s+\w+', l))
axiomatizes_prior_work = 1 if axiom_count > 0 else 0
```

The auditor must write a one-sentence `contribution_statement` before it can set `status='compiled_advance'`. If it can't, the result is `compiled_no_advance`.

### C. CLAUDE.md edit

**Before** (Database table row, line 105):

```markdown
| `submissions` | All Aristotle jobs (with `gap_statement`, `submission_type`, `target_resolved`) |
```

**After:**

```markdown
| `submissions` | All Aristotle jobs. `status` ∈ {submitted, compile_failed, compiled_partial, compiled_no_advance, compiled_advance, disproven}. `target_resolved=1` requires `contribution_statement NOT NULL` AND `axiomatizes_prior_work=0`. |
```

### Rollout / rollback (#2)
1. `cp tracking.db tracking.db.bak.20260528`; `python3 scripts/migrations/run.py`; spot-check 10 rows per new status value.
2. **Rollback:** `mv tracking.db.bak.20260528 tracking.db`.

---

## Proposal #1 — informal-sketch stage (CONFLICTS WITH PRIME DIRECTIVE)

Serious gap-targeting becomes: **Lean statement + ≥150-word informal sketch + 3–5 candidate lemmas**. Bare statements remain allowed (and *required*, as the control arm of the pilot below) for three categories: `submission_type ∈ {falsification, baseline_control, ablation}`. The gate flips from *reject reasoning* to *require reasoning, ban directive language* — except when an explicit allowlisted submission_type is set.

### A. CLAUDE.md edits

**Before — Mission (lines 5–7):**
```
**Solve open mathematical problems** by submitting bare conjecture statements to Aristotle and letting it find novel proofs.

We do NOT develop proof strategies. We do NOT write step-by-step proof outlines. We state the open gap, attach prior Aristotle results as context, and submit. Aristotle constructs the proof.
```

**After:**
```
**Solve open mathematical problems** by pairing a strong informal strategist (Gemini 3 Deep Think / GPT-5.5 Pro) with Aristotle as formalizer.

We write ≥150-word informal sketches with 3–5 candidate lemmas. We do NOT write step-by-step Lean tactics or directive essays. We hand Aristotle the math; Aristotle finds the formal path.
```

**Before — Sketch Format (lines 22–34):** bare 8-line template, "Nothing else."

**After:** same headers (`OPEN GAP`, `Source`, `Domain`, `Status`) plus:
```
INFORMAL SKETCH (150–400 words):
[Mathematical intuition. Why is this plausible? What's the obstruction?
Reference prior Aristotle results from `mk context` by name.]

CANDIDATE LEMMAS (3–5, English only — no Lean tactics):
1. ...
```
Cap goes from 30 → **80 non-blank lines**. Banned: numbered tactic steps, "first prove… then apply…", ASCII Lean proof outlines.

**Before — Hard Rules #2, #3, #6 (lines 41, 42, 45):**
```
2. **Sketches are bare conjecture statements** -- no proof strategy, no lemmas, no guidance
3. **<=30 lines per sketch** -- enforced by pipeline gate, no override
6. **No override on the gap-targeting gate** -- `check_gap_targeting()` rejection is final
```

**After:**
```
2. **Sketches must include informal reasoning** -- ≥150-word sketch + 3–5 candidate lemmas (English). Bare statements allowed for `submission_type ∈ {falsification, baseline_control, ablation}` — preserved as measurable control arms.
3. **<=80 non-blank lines per sketch** -- enforced by gate.
6. **The gate rejects directive language, not reasoning** -- numbered tactic steps, "first prove… then apply…", ASCII Lean outlines fail. Mathematical intuition passes.
```
Rule #12 ("compiled clean != resolved the gap") stays — load-bearing.

### B. Rewrite `scripts/safe_aristotle_submit.py:check_gap_targeting` (lines 155–235)

Same signature, flipped logic. Drop `STRATEGY_PATTERNS`; add `DIRECTIVE_PATTERNS` (numbered tactic steps `^\d+\.\s+(apply|prove|show|use)`, `first … then …` step lists, ASCII Lean fences >5 lines). Add `INFORMAL_REQUIRED`: when `submission_type != 'falsification'`, require ≥150 words outside any Lean fence AND a `CANDIDATE LEMMAS` heading. `MAX_SKETCH_LINES`: 30 → 80. ~40 lines changed; function stays under 100.

### C. New script `scripts/informal_sketch.py` (≤120 lines) — HYBRID mode default

Hybrid (debate-recommended): Gemini 3 Deep Think and GPT-5.5 Pro both generate; Codex (GPT-5.3-Codex) merges/audits into one bounded sketch. `--mode single --model X` falls back to picking one (use for ablations).

```python
#!/usr/bin/env python3
"""Draft informal sketch.

Default mode (hybrid): Gemini 3 Deep Think and GPT-5.5 Pro both generate independent
sketches; Codex merges and audits into one bounded final sketch and writes
submissions/sketches/slot<N>_<id>.txt + a sidecar .provenance.json with
{sketch_model_primary, sketch_model_secondary, sketch_hash, candidate_lemmas_json,
 prior_context_used}. Does NOT submit.

Single mode: pick one model directly (use for the bare-baseline-control arm of
the pilot, or for ablation studies).

CLI:
  informal_sketch.py <problem_id> --slot N [--mode hybrid|single] [--model gemini|gpt55]
"""
import argparse, subprocess, sys, pathlib, hashlib, json, textwrap

def mk(cmd, *a):
    return subprocess.run(["mk", cmd, *a], capture_output=True, text=True).stdout
def call_gemini(p): ...   # uses ~/.config keys
def call_gpt55(p): ...
def call_codex_merge(g, x, ctx): ...   # bounded merge; ≤400 words; no tactics

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("problem_id"); ap.add_argument("--slot", type=int, required=True)
    ap.add_argument("--mode", choices=["hybrid","single"], default="hybrid")
    ap.add_argument("--model", choices=["gemini","gpt55"], default="gemini")
    args = ap.parse_args()
    ctx = mk("context", args.problem_id) + "\n---\n" + mk("failed", args.problem_id)
    base_prompt = textwrap.dedent(f"""\
        Problem: {args.problem_id}
        Prior context: {ctx}
        Write ONLY: 150–400 word sketch + 3–5 English candidate lemmas.
        NO Lean tactics. NO numbered "first… then…". NO directive language.
    """)
    if args.mode == "hybrid":
        g_text = call_gemini(base_prompt); x_text = call_gpt55(base_prompt)
        body = call_codex_merge(g_text, x_text, ctx)
        prov = {"sketch_model_primary": "gemini-3-deep-think",
                "sketch_model_secondary": "gpt-5.5-pro",
                "merge_auditor": "codex-gpt-5.3"}
    else:
        body = (call_gemini if args.model=="gemini" else call_gpt55)(base_prompt)
        prov = {"sketch_model_primary": "gemini-3-deep-think" if args.model=="gemini" else "gpt-5.5-pro",
                "sketch_model_secondary": None, "merge_auditor": None}
    prov.update({"sketch_hash": hashlib.sha256(body.encode()).hexdigest()[:16],
                 "prior_context_used": ctx[:500]})
    out = pathlib.Path(f"submissions/sketches/slot{args.slot}_{args.problem_id}.txt")
    out.write_text(body)
    out.with_suffix(".provenance.json").write_text(json.dumps(prov, indent=2))
    print(out)

if __name__ == "__main__":
    sys.exit(main())
```

### D. `.claude/commands/sketch.md`

Step 3 changes from "Write a .txt file. <=30 lines. No proof strategy." to: "Run `python3 scripts/informal_sketch.py <id> --slot <N>`; review the draft; edit only to fix factual errors or trim directive language." Step 5 reports the new 80-line cap and sketch word count.

### E. `math-forge/hooks/scripts/lean-validator.sh`

Same shape. The regex `Proof Strategy|Key Lemma|...` flips to the new directive patterns. Line-count warning threshold: 30 → 80.

### F. `proof_orchestrator.py` — auto-promote sorry-free Codex proofs to Aristotle axiom-discharge (~15-line change, removes manual gate).

### Rollout / rollback (#1)
1. Land #2 (schema + provenance columns); branch `feat/informal-sketch`; apply B–F.
2. Smoke-test 3 problems (NT, algebra, geom/analysis — **NOT combinatorics**; see Pilot below) — gate accepts informal, rejects directive.
3. Run the **Pilot Experiment** described below — 9 submissions, 3×3 design. Do NOT change default behavior based on anecdote.
4. **Rollback:** `git revert` the branch; `informal_sketch.py` stays (additive).

---

## Pilot Experiment — 12 submissions, 4 × 3 (user override: combinatorics included)

The simplest reversible test that distinguishes "sketches improve outcomes" from "we just changed accounting." All 12 submissions tagged `pattern='informal_sketch_v1'` (or `bare_baseline_v1` for control); each row carries `experiment_arm` and provenance.

### Target selection (4 problems)
Pull from google-deepmind/formal-conjectures, one per domain:
- **Number theory** — one open Erdős-NT problem with `mk context` returning ≥1 prior attempt
- **Algebra** — one open Erdős-algebra problem
- **Geometry or analysis** — one open Erdős-geom/analysis problem
- **Combinatorics** — one open Erdős-combinatorics problem (NOT Tuza nu4 — pick a different one to avoid contamination from the 317-attempt history). User-requested inclusion despite debate recommendation to exclude; lets us test whether sketches help on the historically weakest domain.

### Arms (3 per problem)
| Arm | submission_type | experiment_arm | What's submitted |
|---|---|---|---|
| A: Bare control | `baseline_control` | `bare` | Bare conjecture, ≤30 lines, prior_results auto-context only |
| B: Hybrid sketch-first | `gap_targeting` | `sketch_first` | `informal_sketch.py --mode hybrid` output |
| C: Bare-then-ask | `gap_targeting` | `bare_then_ask` | Bare submission first; on `COMPLETE_WITH_ERRORS` send sketch via `project.ask()` |

### Success hierarchy (per submission)
1. `target_resolved=1` with `axiomatizes_prior_work=0` and `contribution_statement` — real win
2. `compiled_advance` — partial progress, novel non-axiom lemma
3. Reusable non-axiom lemma stored in `proven_theorems`
4. Honest failure note in `contribution_statement`

**Hard failure:** axiom wrapper, tautology, known-result restatement, missing `contribution_statement`.

### Decision rule (when do we make sketches default?)
- **Scale to default** if: 1+ `target_resolved=1` OR ≥2 `compiled_advance` results (across all 3 problems) come from arm B or C and zero come from arm A.
- **Do not scale** if: arm A produces ≥1 `compiled_advance` while B/C produce only hard failures, OR all 3 arms produce zero non-axiom output.
- **Re-design and re-run** if: B and C produce wins only on the same single problem (could be problem-specific, not method-specific).

### Budget cap
12 Aristotle runs + ~8 Gemini/GPT sketch calls (hybrid mode = 2 calls per sketch arm × 4 problems = 8). Hard stop at 12. No "let's just try one more."

---

## Open questions for the user

1. **PRIME DIRECTIVE conflict (decide first).** Research evidence (every confirmed open-Erdős win on Aristotle — #124, #645, #728, #729, #401 — and AlphaProof Nexus's 9/353 result) used informal sketches. Your durable directive is the opposite: "GAP-TARGETING ONLY. Bare conjecture. Zero proof guidance." After the /debate refinement: bare is preserved as an explicit control arm, not eliminated. Pick:
   - **(A) Override** — implement #1 as refined here (bare stays for control/falsification/ablation; sketches required for *serious* gap-targeting). Rewrite the PRIME DIRECTIVE; soften the global-memory entry from "GAP-TARGETING ONLY" to "GAP-TARGETING + INFORMAL SKETCH for serious attempts; bare for controls."
   - **(B) Pilot-only** — keep PRIME DIRECTIVE in effect, but run the 9-submission Pilot under a `pattern='informal_sketch_v1'` flag exemption from the gate. Decide on (A) vs revert only after Pilot data lands.
   - **(C) Keep, pick differently** — ship #2 (schema honesty) and the provenance columns now; do not run the Pilot or implement #1. Revisit only after 30 days of clean data confirms bare-only continues at 0/N.

2. **Model design for `informal_sketch.py`** — debate recommendation (with updated models: Gemini 3.1 Pro **Deep Think** + GPT-**5.5** Pro + Codex/GPT-5.3-Codex merge) is **hybrid**. Cost is ~3x a single call but addresses provenance and avoids premature single-model commitment. Pick:
   - **(A) Hybrid by default** (debate-recommended) — `--mode hybrid` is the default; `--mode single --model X` only for the ablation arm of the Pilot.
   - **(B) Single by default** — pick Gemini Deep Think OR GPT-5.5 Pro as default; hybrid only on `--mode hybrid`. Cheaper but loses the dual-source provenance signal.

7. **Gemini variant for sketches** — VERIFIED (May 28 2026 latest):
   - **(A) Gemini 3 Deep Think** (best fit IF accessible) — Google's reasoning specialist; just got a major upgrade explicitly built for research scientists. New SOTA: 48.4% HLE, 84.6% ARC-AGI-2, IMO 2025 gold. **Access gated**: Google AI Ultra in app; Gemini API requires early-access enrollment at https://ai.google.dev/gemini-api/docs — you may need to opt in.
   - **(B) Gemini 3.1 Pro standard** (proven on our exact problem class) — what AlphaProof Nexus used for its 9-Erdős result May 2026. 1M context. Generally available via standard Gemini CLI. Safe default if Deep Think API access isn't granted yet.
   - **Recommendation**: try (A) first; if `gemini` CLI / API rejects with access-denied, fall back to (B). Note in `provenance.json` which one was actually used.

8. **Verify before pilot** — three CLI checks to run:
   - `codex --version` — confirm GPT-5.3-Codex (or newer) is the backend
   - `gemini --model gemini-3-deep-think --help` — confirm Deep Think is accessible
   - `gemini --model gemini-3.1-pro --help` — confirm standard Pro is accessible (fallback)

## ⚠️ MODEL-ACCESS BLOCKER (verified May 28 2026)

Live probes on this machine reveal we **cannot run the pilot as designed** without remediation:

| Tool | Version | Backing model | Status |
|---|---|---|---|
| `codex` CLI | 0.130.0 | self-reports "GPT-5" (not GPT-5.3-Codex, not GPT-5.5 Pro) | ⚠️ outdated backend |
| `gemini` CLI | 0.25.2 | only `gemini-2.5-flash` and the unspecified default respond; `gemini-3-deep-think`, `gemini-3.1-pro`, and `gemini-3.5-flash` all return `ModelNotFoundError` | ⚠️ credentials/tier need refresh |

This is the **same Gemini ModelNotFoundError that broke 2/3 voices in the /debate earlier today** — not a transient issue.

**Remediation needed before pilot can run:**

1. **Gemini access**:
   - `gemini /auth` to refresh OAuth + scopes
   - Confirm Google AI Ultra or Workspace tier (Deep Think requires Ultra; 3.1 Pro requires at least a paid tier)
   - For Deep Think specifically: enroll in early-access at https://ai.google.dev/gemini-api/docs (gated)

2. **Codex / GPT-5.5 Pro access**:
   - `codex update` to bump CLI to latest
   - `codex -m gpt-5.5-pro --help` after update to confirm the new model is selectable
   - May require ChatGPT Pro / API tier with GPT-5.5 Pro entitlement

3. **Fallback path if upgrades aren't immediate**:
   - Use Codex CLI default (GPT-5) as merge-auditor
   - Use `gemini-2.5-flash` as the Gemini side (significantly weaker than 3.1 Pro / Deep Think; pilot results will under-represent the approach's true potential)
   - Mark all pilot runs with `provenance.json.sketch_model_primary='gemini-2.5-flash'` so we know not to over-interpret results
   - Re-run on the better models once access is sorted

3. **Schema migration scope** — apply to all 1,157 historical rows (cleaner, rewrites old labels) or only new submissions (additive, leaves history messy)?

4. **Auto-promote sorry-free Codex proofs** to Aristotle automatically (#1.F) or require manual approval per promotion (preserves current control point)?

5. **Combinatorics in the Pilot** — RESOLVED: user chose **(B) include**. 12 submissions, 4 domains × 3 arms. Combinatorics problem must NOT be Tuza nu4 (avoid contamination from 317-attempt history).

6. **Pilot promotion threshold** — RESOLVED: user chose **(A) strict** — 1+ `target_resolved=1` OR ≥2 `compiled_advance` with zero arm-A wins.
