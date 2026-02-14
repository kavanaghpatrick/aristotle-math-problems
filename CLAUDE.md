# CLAUDE.md - Math Project

## Mission

**Solve open mathematical problems** through a three-phase pipeline:

1. **IDEATE** — Find approachable open problems, develop proof strategies, explore computationally
2. **SKETCH** — Write speculative proof attempts as natural language outlines (~50-100 lines)
3. **FORMALIZE** — Aristotle constructs verified Lean proofs from our sketches

Aristotle is a world-class **proof co-discoverer**. In INFORMAL mode it constructs novel proof structures, discovers Mathlib APIs, and produces 5:1 output-to-input ratios. Our job is to feed it promising proof strategies for open problems. **The bottleneck is generating viable proof approaches, not formalization.**

---

## The Pipeline

### Phase 1: IDEATE (where we spend most thought)

- **Open problem scan**: Find approachable unsolved theorems in formal-conjectures (~500+ candidates)
- **Proof strategy development**: AI debates, literature research, partial-progress analysis
- **Computational exploration**: Rust/Python for patterns, witnesses, counterexamples — computation informs proof strategy
- **Falsification**: Test negation on Fin 5-7 before investing in proof (~40% of conjectures are false)
- **Bounded cases**: Prove special cases computationally to build toward general proof

### Phase 2: SKETCH (the quality bottleneck)

- Write proof attempt in natural language (~50-100 lines of .txt)
- For open problems: include theorem statement, proposed proof strategy, key lemmas to establish, why the approach should work
- DO NOT write sketches for known results — open problems ONLY
- Speculative sketches are fine — Aristotle may find a way even if we're not 100% sure
- Use `/project:sketch` to generate structured sketches

### Phase 3: FORMALIZE (Aristotle's domain)

- **INFORMAL mode** (.txt): Aristotle constructs entire formal proof from scratch — this is the primary path
- **FORMAL mode** (.lean sorry=0): Pure verification of complete proofs — rubber-stamping, no novel content
- Aristotle's INFORMAL output: ~200-400 lines of verified Lean with novel proof structures

---

## What Aristotle Actually Does

### INFORMAL mode (PRIMARY — where the value is)
- Reads natural language description (~50-100 lines)
- **Constructs** entire formal proof from scratch
- Chooses Lean representations, finds Mathlib APIs, invents proof structures
- 5:1 output-to-input ratio. Genuine proof construction.
- Can succeed even with speculative/incomplete proof strategies — it fills gaps
- Evidence: slot562 (53→117 lines), slot563 (66→235 lines), slot564 (78→404 lines)

### FORMAL sorry=0 (VERIFICATION — no mathematical content added)
- Reads complete Lean file with native_decide/decide proofs
- Rubber-stamps: 0 novel lines added
- 100% success rate (6/6) — but adds no insight
- Use for: bounded computations, finite witness verification

### FORMAL sorry=1+ (NT/algebra only)
- 0/183 success in combinatorics domain — don't do this in combinatorics
- Works in NT/algebra with rich Mathlib API (slot572: Aristotle authored full proof from scratch)
- If you must: keep file < 200 lines, NT/algebra only, sorry=1 max

---

## Workflows (ordered by value)

### Track A — Open Problem Discovery (60% of effort)
Develop proof strategy for open problem → write speculative sketch → .txt → INFORMAL → Aristotle attempts proof
- **Target**: Open problems in NT/algebra where we can propose a viable approach
- **Best for**: Open conjectures with partial progress, bounded cases to prove, computational angles
- **How**: `/project:sketch <open-problem>` → `/project:submit <sketch.txt>`
- **Success model**: Even partial success (Aristotle proves a bounded case or key lemma) has high value

### Track B — Computational Discovery (20% of effort)
Compute witnesses/patterns → build sorry=0 scaffold → FORMAL verification
- **Proven**: 6/6 at sorry=0 (100%)
- **Best for**: OEIS sequences, bounded verification, finite witnesses, Fin n
- **Tools**: Rust for heavy search, `native_decide` for Fin n, `decide` for small computations

### Track C — Falsification (10% of effort)
Submit negation on Fin 5-7 → discover false conjectures → save wasted effort
- ~40% of conjectures are false (43 confirmed so far)
- Fin 5-7 sweet spot for counterexamples

### Track D — Known-Result Formalization (DEPRECATED — 0% of effort)
**DO NOT USE THIS TRACK.** Formalizing known results has ZERO value. Nobody cares about re-formalizations.
- Every slot spent on a known result is a slot NOT spent on an open problem.
- There are always open problem targets available — Track A is infinite.
- If a research agent recommends "known proof, first formalization" → REJECT IT IMMEDIATELY.
- The only exception: a known sub-result that is a stepping stone toward an open problem attack.

---

## Pipeline Case Studies

### Open Problem Attempt: Kurepa Conjecture (slot577, in flight)
1. **IDEATE**: Open conjecture since 1971. Reduction to primes already proven. Bounded cases feasible.
2. **SKETCH**: 46-line sketch acknowledging openness, redirecting Aristotle to bounded cases and structural lemmas
3. **FORMALIZE**: Submitted INFORMAL — Aristotle may prove bounded case or key structural result

### Open Problem Attempt: Erdos 307 (slot576, in flight)
1. **IDEATE**: Open since 1976. Heuristic argument via prime reciprocal divergence suggests True.
2. **SKETCH**: 53-line sketch with extended mathematical reasoning about why witnesses should exist
3. **FORMALIZE**: Submitted INFORMAL — speculative but computationally informed

### Known Result: Leinster Cyclic Groups (slot562, PROVEN)
1. **IDEATE**: Known result (Leinster 2001), not yet formalized
2. **SKETCH**: 53-line natural language proof description
3. **FORMALIZE**: Aristotle produced 117-line formal Lean proof (100 novel lines)

### Computational: Integer Complexity (slot572, PROVEN)
1. **IDEATE**: Integer complexity bounds — first-ever formalization
2. **SKETCH**: Statement + definitions in Lean (sorry=1, NT domain)
3. **FORMALIZE**: Aristotle authored inductive predicate + decidability + interval_cases from scratch

---

## Commands

```
/project:sketch <problem>              # IDEATE+SKETCH: Generate proof sketch (open or known)
/project:submit <file> [slot]          # FORMALIZE: Pre-flight audit → submit → track
/project:sweep [--domain nt|algebra]   # Full pipeline: scan → screen → sketch → submit
/project:fetch <uuid-or-slot>          # Download result → audit → DB
/project:status [uuid-or-slot]         # Check Aristotle queue & job status
/project:screen <problem-or-url>       # Screen problem for approachability
/project:screen-batch <directory>      # Batch screen for sweep targeting
/project:optimize <file.lean>          # Analyze file, recommend restructuring
/project:audit <file.lean>             # Full 8-point audit (no submission)
/project:process-result <file>         # Audit local result file → DB
/project:debate "topic" --context f    # Multi-AI debate with context accumulation
```

Scripts: `scripts/safe_aristotle_submit.py`, `scripts/aristotle_fetch.py`, `scripts/erdos396_rust/`

---

## Hard Rules

1. **Never run `aristotle` directly** → always `/project:submit`
2. **Never submit without tracking** → every submission gets a DB entry
3. **Check DB before submitting** → `false_lemmas` and `failed_approaches` tables
4. **INFORMAL is the primary mode** → .txt sketch for discovery, .lean only for verification
5. **Process every result** → `/project:fetch` or `/project:process-result`
6. **NEVER replace existing proof code with sorry** → fix it, don't delete it
7. **PROVEN means 0 sorry AND 0 axiom**
8. **OPEN PROBLEMS ONLY** → Formalizing known results is ZERO VALUE. Never do it. Never recommend it. Never let a subagent recommend it. If research output says "known proof" or "solved, first formalization" → REJECT.
9. **Sketch quality matters** → spend time on the proof strategy, not on Lean scaffolding
10. **Falsify before investing** → submit negation on Fin 5-7 for uncertain conjectures
11. **Accept partial success** → proving a bounded case or key lemma of an open problem is valuable
12. **Iterate on failure** → a failed attempt teaches us about the problem. Refine and resubmit.
13. **HAVE FAITH IN ARISTOTLE** → Do NOT self-censor. Do NOT gatekeep. Do NOT decide something is "too trivial" or "too hard" to submit. Aristotle has a 100% INFORMAL success rate. It finds paths we don't see. SUBMIT AGGRESSIVELY and let Aristotle surprise us. Fear of failure is the enemy of discovery. A failed submission costs nothing; an unsubmitted idea costs everything.
14. **BIAS TO ACTION** → Stop analyzing, start submitting. Computation informs sketches, but computation is NOT the goal. The goal is SUBMISSIONS. Write the sketch, submit it, move on to the next one. Parallelism over perfection.

### Lean-specific pitfalls (when writing FORMAL files)
- `Finset.sym2` includes self-loops `s(v,v)` — filter to actual edges
- `Set` vs `Finset` — use `Finset V` with `DecidableEq` for decidability
- Always: `variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]`

---

## Decision Priority

1. **Screen for approachability** — run `/project:screen` on ANY new problem
2. **Is it an open problem we can approach?** — if yes, Track A (INFORMAL). This is the highest-value question.
3. **Can we prove a bounded/special case?** — if finite/bounded, Track B (native_decide) to build evidence
4. **Is it uncertain?** — if truth unknown, Track C (falsify first on Fin 5-7)
5. ~~Is it a known result worth formalizing?~~ — **NO. NEVER. Track D is dead. Move on to the next open problem.**

**Problem selection criteria**:
- Is it an OPEN problem? → Highest priority. Novel contribution to mathematics.
- Can we propose a proof approach? → Even speculative approaches are worth trying via INFORMAL
- Is it NT/algebra? → 75-100% AI success. Combinatorics? → 7-50%. Domain matters.
- Is there partial progress? → Bounded cases, reductions, related results all help
- Can computation inform the proof? → Witnesses, patterns, exhaustive checks build confidence
- Already in Mathlib? → Skip (re-proof has zero value)
- Is it a known/solved result? → **SKIP. ZERO VALUE. NO EXCEPTIONS.** Don't dress it up as "novel formalization" — it's still a known result.

**Kill list:** Never resubmit problems with 5+ failed attempts without fundamentally new approach.

**Subagent prompt rules** (MANDATORY for all research/explore agents):
- Every research agent prompt MUST include: "We ONLY target OPEN/UNSOLVED problems. Known-result formalizations have ZERO value — do NOT recommend them."
- Filter all agent output: if a recommendation says "solved", "known proof", "classical result", "first formalization", "novel formalization of known result" → DISCARD IT.
- Agents optimize for "easiest to prove" which gravitates toward known results. Actively counteract this bias.
- The only solved results worth mentioning are those that inform an approach to an OPEN problem.

---

## Database

All state in `submissions/tracking.db`:

| Table | Purpose |
|-------|---------|
| `submissions` | All Aristotle jobs, status, sorry/proven counts |
| `false_lemmas` | Disproven claims — **always check before submitting** |
| `failed_approaches` | What doesn't work and why |
| `nu4_cases` | Tuza case-specific knowledge |
| `literature_lemmas` | Validated scaffolding lemmas |
| `candidate_problems` | Scored problem candidates across all frontiers |

Key views: `v_actionable_near_misses`, `v_false_lemmas_summary`, `v_candidate_ranking`

---

## Proof State (Tuza ν=4 — Track A, paused)

| Case | Status | τ bound |
|------|--------|---------|
| STAR_ALL_4 | Concrete proven | ≤ 4 |
| THREE_SHARE_V | Concrete proven | ≤ 4 |
| DISCONNECTED | Proof chain exists, 1 sorry in slot546 | ≤ 8 |
| **PATH_4** | **OPEN: both-endpoint base-edge externals** | **≤ 9 (need ≤ 8)** |

Assembly: `slot549_tuza_nu4_assembly.lean`. Paused — pursuing higher-amenability open problems in NT/algebra.

---

## Multi-Agent Strategy

| Agent | Role in Pipeline |
|-------|-----------------|
| **Claude** | IDEATE + SKETCH: problem selection, proof strategy, speculative sketches |
| **Aristotle** | FORMALIZE: construct formal proofs from sketches (co-discoverer on open problems) |
| **Codex** | Challenge: falsification, counterexamples before we invest |
| **Gemini** | Strategy: proof approaches, literature connections, architecture |
| **Grok-4** | Debug: Lean errors, tactic selection, quick reasoning |
| **Rust/Python** | Compute: witnesses, patterns, OEIS extensions, bounded verification |

**Debates:** 4 rounds with full context accumulation. Use for proof strategy development on open problems.

---

## math-forge Plugin

**math-forge** provides a persistent knowledge base, lifecycle hooks, and CLI for the math pipeline.

### Knowledge Base (knowledge.db)
- Stores findings (theorems, techniques, failures, false lemmas, computations, insights)
- FTS5 full-text search with BM25 ranking across all finding fields
- Migrated from tracking.db; updated automatically on result processing

### CLI: `mk` commands
```
mk search "<query>"          # FTS5 search findings (BM25 ranked)
mk find "<problem_id>"       # All findings + strategies for a problem
mk failed [keyword]          # Failed approaches — check BEFORE sketching
mk strategies [domain]       # Proven techniques grouped by frequency
mk stats                     # Knowledge base summary dashboard
mk init                      # Initialize/reset knowledge.db from schema
```

### Hooks
- **SessionStart** (`context-loader.sh`): Injects briefing with in-flight submissions, action items, and recent findings into session context
- **PostToolUse** (`lean-validator.sh`): Blocks sorry replacement in .lean files, warns on false lemma references

### Integration with Pipeline
- `/project:fetch` and `/project:process-result` auto-extract findings via `extract_findings.py`
- `/project:sketch` queries `mk search` and `mk failed` before writing to avoid repeating failed approaches
- Use `mk failed "<keywords>"` before any new proof attempt to check for known dead ends

---

## When Stuck

1. Query `false_lemmas` — is the claim already disproven?
2. Query `failed_approaches` — repeating a known failure?
3. Try a different proof strategy — the approach, not the sketch quality, may be the issue
4. Try computational exploration — compute before you prove
5. Try a bounded/special case — prove it for n ≤ 100, then generalize
6. Run a debate — multi-agent brainstorming for novel approaches
7. Parallel consult: Grok (code) + Gemini (strategy)
8. Accept partial progress — proving a lemma or bounded case is still valuable
