# Merged Aristotle Solvability Taxonomy (May 30, 2026)

**Author:** Agent #8 of 10 (Erdős labeling sweep)
**Sources merged:**
- Codex taxonomy (8 dimensions, agent #5) — `codex_labeling_taxonomy.md`
- Grok taxonomy (6 dimensions, agent #7) — `grok_labeling_taxonomy.md`
- Gemini taxonomy (agent #6, rate-limited; placeholder)
- Aristotle Advance DNA (agent #2) — 8 snipe signatures S1-S8
- Failure DNA Catalog (agent #3) — 10 failure modes F1-F10
- Feasibility Filter Rubric — 5 categories
- Gemini placeholder

**Purpose:** Each open conjecture in formal-conjectures gets a row of orthogonal labels predicting Aristotle snipe probability.

---

## The Six Dimensions

After taking the **union** of all proposed axes and dropping redundancies, six dimensions cover everything that empirically matters:

### D1. `feasibility_category` (from rubric)

Values: `finite-verification`, `constructive-search`, `mechanical-extension`, `structural-open`, `known-formalization`

This is the master classifier (already enforced by `feasibility_filter_rubric.md`). All other dimensions are sub-discriminators.

### D2. `quantifier_geometry` (Codex D2, Grok Axis 1 partial)

Values: `bounded-finite`, `fixed-finite-object`, `finite-reducible-infinite`, `infinite-parametric`, `full-structural`

Decision rule: parse the outer quantifiers of the main `research open` theorem.

- `bounded-finite`: `∀ n ≤ N` or `∀ n ∈ Finset.range N` with concrete N
- `fixed-finite-object`: a single object with a finite check (e.g., specific graph, polynomial)
- `finite-reducible-infinite`: claim is `∀ n` or `∃ n` but a bounded analogue is the gap (Brocard pattern)
- `infinite-parametric`: `∀ p : ℕ, p.Prime → ...` — parametric infinite family
- `full-structural`: `∀ f : ℕ → ℕ, ...`, `∀ A : Set ℕ, ...`, `Set.Infinite`, `Tendsto`, `Irrational`, density claims

### D3. `certificate_shape` (Codex D3, Grok Axis 2)

Values: `explicit-witness`, `small-table`, `greedy-CRT`, `algorithmic-search`, `descent-ready`, `universal-negative`, `pure-existence`, `none-known`

Decision rule: what would a successful Lean proof actually check?

- `explicit-witness`: a single concrete number/object closes the gap
- `small-table`: 10-1000 cases verifiable by `native_decide`
- `greedy-CRT`: covering system / set cover constructible by greedy + CRT
- `algorithmic-search`: requires polynomial-time search bounded
- `descent-ready`: Fermat infinite descent / 2-descent / mod-p reduction with explicit small primes
- `universal-negative`: "no solution exists" — needs structural elimination
- `pure-existence`: "there exists" with no witness recipe
- `none-known`: structural barrier; no certificate identifiable

### D4. `snipe_signature_match` (from advance_dna)

Values: `S1-decide`, `S2-table-bridge`, `S3-residue-fermat`, `S4-greedy-CRT`, `S5-case-split`, `S6-graph-cex`, `S7-algebraic-witness`, `S8-negative-shape`, `none`

Decision rule: does the problem match one of the 8 demonstrated Aristotle snipe templates?

- S1: bounded-N + decidable predicate → `native_decide`
- S2: witness table + `Nat.nth_count` bridge
- S3: residue class + Fermat reduction
- S4: 2D cover + CRT witness
- S5: case-split + σ₀ multiplicativity
- S6: explicit small graph counterexample
- S7: algebraic witness verification (Mathlib-heavy)
- S8: structural constraints on counterexample shape (compiles but no advance per user)

### D5. `failure_mode_risk` (from failure_dna)

Values: `low`, `F1-iff-rfl`, `F3-side-lemma-bloat`, `F4-axiomatize-hard`, `F5-recursive-falsify`, `F6-restate-sorry`, `F7-bounded-leak`, `F8-vacuous-iff`, `F9-compute-explosion`, `F10-def-mismatch`

Decision rule: which `compiled_no_advance` trap is most likely?

- `F1-iff-rfl`: non-decidable wrapper (`Irrational`, `Tendsto`, density without finite restriction)
- `F3-side-lemma-bloat`: structural with no finite reduction; Aristotle produces 1000-line infrastructure
- `F7-bounded-leak`: unbounded universal that Aristotle answers with a 1000-range partial answer
- `F8-vacuous-iff`: `answer ↔ <verbatim definition>` via `Iff.rfl`

### D6. `negative_evidence` (Codex D8)

Values: `untouched`, `attempted-low` (≤ 2 submissions, no advance), `attempted-medium` (3-5), `attempted-high` (6+), `disproven-clean`, `project-carcass` (10+ no_advance like tuza_nu4)

Decision rule: query `submissions/tracking.db` for problem_id. Aliases must be resolved (`erdos_647` = `erdos647`).

### D7. `formalization_surface` (Codex D5, Grok Axis 6) — implicit, embedded in snipe_score

Mathlib-native vs theory-heavy. Number theory primitives (`Nat.Prime`, `totient`, `σ`, `divisors`, `Nat.factorial`, modular arithmetic) are mathlib-native — high feasibility. Analytic number theory, L-functions, elliptic curves, advanced graph Ramsey theory, large cardinals — theory-heavy, low feasibility.

---

## Snipe Score (1-10)

Single composite score derived from the dimensions:

```
score = 5 (base)
  + 4 if S1-decide / S6-graph-cex match (proven reproducible)
  + 3 if S2-table-bridge / S5-case-split / S3-residue-fermat match
  + 2 if S4-greedy-CRT / S7-algebraic-witness match
  + 0 if S8 (compiles but doesn't advance)
  - 4 if full-structural + none-known certificate
  - 3 if F1-iff-rfl risk
  - 3 if F3-side-lemma-bloat risk (unbounded + no finite reduction)
  - 2 if attempted-high (6+ submissions, 0 advance)
  - 5 if project-carcass
  + 1 if mathlib-native
  - 1 if theory-heavy (elliptic curves, hypergraph Ramsey, transfinite ordinals)
Clamp to [1, 10]
```

---

## Recommended Next Action

Values: `SUBMIT_NOW`, `DRAFT_FIRST`, `RESEARCH_REQUIRED`, `AVOID`, `ALREADY_TRIED_RECENT`

Decision rule:

| Condition | Action |
|---|---|
| score ≥ 7 AND untouched/attempted-low | `SUBMIT_NOW` |
| score 5-6 AND finite-verification/constructive-search | `DRAFT_FIRST` |
| score ≤ 4 OR F1/F3 risk dominant | `RESEARCH_REQUIRED` |
| project-carcass OR attempted-high with 0 advance | `ALREADY_TRIED_RECENT` |
| structural-open + no fresh diagnostic + theory-heavy | `AVOID` |
| `known-formalization` per rubric | `AVOID` (excluded from active rotation) |

---

## Decision Procedure

1. Read the main `@[category research open]` theorem.
2. Identify quantifier geometry (D2).
3. Identify what a successful Lean proof would check (D3 certificate shape).
4. Match against snipe signatures S1-S8 (D4).
5. Identify dominant failure mode risk F1-F10 (D5).
6. Query DB for attempt history → D6.
7. Compute snipe_score and pick `recommended_next_action`.

---

## Use Notes

- The 8 snipe signatures are **demonstrably reproducible** (n ≥ 2 each); they are the strongest priors.
- The 10 failure modes are **the dominant trap on `compiled_no_advance`** outcomes.
- A `score ≥ 7` problem without snipe-signature match is rare and represents the actual "snipe" lane.
- A `score ≤ 3` problem with no advance is a confirmed `AVOID`.

Authority trail: feasibility_filter_rubric.md is binding policy. This taxonomy adds **labels for ranking**; it does not relax the gate.
