# CLAUDE.md - Math Project

## Mission
Solve open mathematical problems using Aristotle as a **formalization engine**. Primary: Formal Conjectures sweep (NT/algebra). Secondary: Tuza ν=4 (6/7 done, gated). Falsify false conjectures fast. Prove true ones with scaffolding or Boris workflow.

---

## How Aristotle Works

**Always aim for sorry=0 before submitting.** This is by far the most reliable path. sorry=1 in a short, focused file sometimes works. sorry=2+ essentially never works — split or use INFORMAL mode instead.

**What works:**
- `native_decide` on `Fin n` — the dominant proof-closing tactic in successful files
- Thematic batches — same template adapted per case
- Falsification on `Fin 6-7` — submit the negation before investing in a new lemma
- Scaffolding helps YOU reach sorry=0 (it doesn't independently help Aristotle)

**Submission modes:**
- **FORMAL_LEAN** (.lean) — default for verification of complete proofs
- **INFORMAL** (.txt) — Aristotle rewrites from scratch. Use for Boris workflow or discovery
- Use `admit` (not `sorry`) for goals you don't want Aristotle to attempt
- **PROVIDED SOLUTION**: Natural language proof sketch in header comments guides MCTS search

**Three workflows (choose based on /project:screen results):**
- **Track 1 — native_decide**: sorry=0 scaffold tower, Fin n, 77% success rate
- **Track 2 — Boris INFORMAL**: Claude generates proof sketch → INFORMAL mode → Aristotle formalizes (~45% external success rate, untested by us)
- **Track 3 — Falsification**: Submit negation on Fin 5-7, ~40% of conjectures are false

**What Aristotle cannot reliably do:**
- Fill sorry gaps in combinatorics — 0/183 in our domain (but works for NT/algebra)
- Handle files that don't compile — pre-check syntax before submitting
- Max 2 resubmissions per formulation without a major rewrite

---

## Commands

```
/project:submit <file.lean> [slot]   # Pre-flight audit → submit → track
/project:optimize <file.lean>        # Analyze file, recommend restructuring
/project:fetch <uuid-or-slot>        # Download completed result → audit → DB
/project:status [uuid-or-slot]       # Check Aristotle queue & job status
/project:process-result <file>       # Audit local file → DB update
/project:audit <file.lean>           # Full 7-point audit (no submission)
/project:screen <problem-or-url>     # Screen problem for AI amenability (6 gates + 7 scores)
/project:screen-batch <directory>    # Batch screen Lean files for sweep targeting
/project:debate "topic" --context f  # Multi-AI debate with full context accumulation
```

Scripts: `scripts/safe_aristotle_submit.py`, `scripts/aristotle_monitor.py`

---

## Hard Rules

1. **Never run `aristotle` directly** → always `/project:submit`
2. **Never submit without tracking** → every submission gets a DB entry
3. **Near-misses get worked IF the gap is solvable** → check if blocked by falsified approach first, then prove locally, resubmit sorry=0
4. **Check DB before submitting** → `false_lemmas` and `failed_approaches` tables
5. **Include proven scaffolding** → full proofs, never sorry placeholders
6. **Process every result** → `/project:fetch` or `/project:process-result`
7. **NEVER replace existing proof code with sorry** → fix it, don't delete it
8. **PROVEN means 0 sorry AND 0 axiom**
9. **No self-loops** → `s(v,v)` is not a graph edge
10. **NEVER use `A.sym2` for edge enumeration** → `Finset.sym2` includes self-loops! Use explicit edges
11. **Default to `FORMAL_LEAN` mode** → use INFORMAL (.txt) only for discovery submissions with sorry≥2

---

## Decision Priority

1. **Screen before attacking** — run `/project:screen` on ANY new problem. Gates must pass.
2. **Formal Conjectures sweep (75%)** — clone google-deepmind/formal-conjectures, filter for NT/algebra + finite structure, falsify then prove
3. **Gated Tuza (25%)** — INFORMAL mode only for 50 slots. Formalize only if sketch emerges.
4. **Falsify uncertain conjectures** — submit negation on Fin 5-7 BEFORE investing in proof
5. **0% on infinite-domain problems** — Erdos-Straus, Seymour n≥15, Brocard (gates fail)

**Problem selection thesis**: `docs/PROBLEM_SELECTION_THESIS.md`
**Kill list:** Never resubmit problems with 3+ failed attempts without a fundamentally new approach. Check `failed_approaches` first.
**Domain rule:** Prefer NT/algebra (AI 75-100%) over combinatorics (AI 7-50%). Domain is THE predictor of success.

---

## Database

All state in `submissions/tracking.db`:

| Table | What's In It |
|-------|-------------|
| `submissions` | All Aristotle jobs, status, sorry/proven counts |
| `false_lemmas` | Disproven claims — **always check before submitting** |
| `failed_approaches` | What doesn't work and why |
| `nu4_cases` | Case-specific knowledge, approaches, next actions |
| `literature_lemmas` | Validated scaffolding lemmas |
| `candidate_problems` | Scored problem candidates across all frontiers |

Key views: `v_actionable_near_misses`, `v_false_lemmas_summary`, `v_candidate_ranking`

---

## Proof State

Most proven files already use abstract `SimpleGraph V`. The formalization infrastructure exists — the gap is mathematical.

| Case | Status | τ bound |
|------|--------|---------|
| STAR_ALL_4 | Concrete proven, general needs formalization | ≤ 4 |
| THREE_SHARE_V | Concrete proven, general needs formalization | ≤ 4 |
| DISCONNECTED (incl. cycle_4) | Proof chain exists, 1 sorry in slot546 | ≤ 8 |
| **PATH_4** | **OPEN: both-endpoint base-edge externals** | **≤ 9 (need ≤ 8)** |

**Assembly:** `slot549_tuza_nu4_assembly.lean` — only PATH_4 both-endpoints is genuinely unresolved.

**Frontier approach:** Modified partition — group S_A∪S_B, apply Parker (nu≤3 → τ≤6), then τ(S_C)+τ(S_D)≤2 each = total 8.

---

## Lean Pitfalls

- `Finset.sym2` includes self-loops `s(v,v)` — filter to actual edges or enumerate explicitly
- `Set` vs `Finset` — use `Finset V` with `DecidableEq` for decidability
- Always: `variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]`

---

## Multi-Agent Strategy

| Agent | Use For |
|-------|---------|
| **Codex** | Challenge claims BEFORE submitting — best at falsification and finding counterexamples |
| **Gemini** | Audit proof completeness, find missing patterns, literature connections |
| **Grok-4** | Fix specific Lean errors, variable mismatches, tactic selection |
| **Aristotle** | Verify sorry=0 files. Falsify uncertain claims on Fin 6-7 |

**Debates:** Use 4 rounds with full context accumulation. Round 2 is where insights emerge. 2-round debates are too shallow.

---

## When Stuck

1. Query `false_lemmas` — is the claim already disproven?
2. Query `failed_approaches` — repeating a known failure?
3. Query `nu4_cases` — what's the current approach for this case?
4. Parallel consult: Grok (code) + Gemini (strategy)
