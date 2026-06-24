# Long-Tail Erdős Snipe Candidates — Agent S5 (2026-05-30)

**Mission**: Mine the long-tail of obscure Erdős problems — Tao's identified AI sweet spot. Filter the 805-statement registry to find problems Aristotle can plausibly close that nobody is actively pushing.

**Inputs:**
- `open_problems_registry_may30.csv` (805 verified-open, 493 Erdős-tagged, 319 distinct problem_ids)
- `literature_kill_list.csv` (26 AI-closed)
- `ai_competition_audit_may30.csv` (24 problems with active AI competition)
- `advance_dna_may30.md` (S1-S8 snipe signatures)
- erdosproblems.com forum activity (90+ candidate pages curl'd)

**Filtering pipeline:**
1. 493 Erdős-tagged → 455 VERIFIED_OPEN (38 POSSIBLY_SOLVED_SINCE excluded)
2. → 415 with ≤1 prior Aristotle attempt
3. → 252 after removing the famous-deep / current closure list / kill list (incl. newly-discovered SOLVED #318, #868, and #488 with Aristotle prior)
4. → 72 root-statement theorems with snipe-signature match ≥ S?-INF after pure-asymptotic / cardinal / irrationality filtering
5. → **50 final candidates** ranked by composite (snipe × 0.45 + closure × 0.35 + neglect × 0.20)

**Counts after filtering:**
- S7 (explicit-witness, witness construction): 35
- S1 / S1/S5 (bounded native_decide / structural finiteness): 12
- S6 / S6/S7 (small graph counterexample): 3

**Domain distribution:** NT 35; combinatorics 10; geometry 2; algebra 2; analysis 1.

---

## Top 15 Long-Tail Snipes

| # | Erdős | Theorem | Sig | sn | cl | ne | Lane | One-line statement |
|---|---|---|---|---|---|---|---|---|
| 1 | **#373** | `erdos_373.variants.suranyi` | S1/S5 | 8 | 8 | 10 | bounded+structural | `{(n,a,b) | n!=a!·b!, 1<b≤a, a+1≠n} = {(10,7,6)}` — Surányi's factorial-product classification, only (6,7,10) known |
| 2 | **#944** | `erdos_944.dirac_conjecture.k_eq_four` | S6 | 8 | 8 | 10 | graph-witness | ∃ 4-critical graph with NO critical edge — Dirac 1970 conj, $k=5$ solved (Brown 1992), $k=4$ still open |
| 3 | **#141** | `erdos_141.variant.eleven` | S7 | 8 | 7 | 10 | explicit-witness | ∃ 11 CONSECUTIVE primes in AP — verified to k=10, k=11 open (NOT Green-Tao territory: this is *consecutive*) |
| 4 | **#324** | `erdos_324.variant.quintic` | S1 | 8 | 7 | 10 | bounded-witness | `{(a,b) | a<b}.InjOn (a^5+b^5)` — Sidon-like sumset, decidable bounded check up to small N |
| 5 | **#100** | `erdos_100_piepmeyer` | S7 | 7 | 6 | 10 | explicit-witness | ∃ 9 unit-separated points in ℝ² with diam<5 — Piepmeyer's construction, pure finite witness |
| 6 | **#1041** | `erdos_1041` | S7 | 7 | 6 | 10 | explicit-witness | Erdős-Herzog-Piranian: ∃ path of length <2 in `{|f|<1}` joining two roots — explicit polynomial witness |
| 7 | **#1055** | `erdos_1055.variants.selfridge_limit` | S7 | 7 | 6 | 10 | explicit-witness | Selfridge prime-class bound: ∃ M, ∀r, (p_r)^(1/r) ≤ M |
| 8 | **#329** | `erdos_329.of_sub_perfectDifferenceSet` | S7 | 7 | 6 | 10 | explicit-witness | Sidon → PerfectDifferenceSet structural implication |
| 9 | **#329** | `erdos_329.converse_implication` | S7 | 7 | 6 | 10 | explicit-witness | Converse of Sidon-density-1 implication |
| 10 | **#373** | `erdos_373.variants.maximal_solution` | S1 | 7 | 6 | 10 | bounded-witness | `(16, [14,5,2])` is the maximal n for `n! = ∏ a_i!` — bounded check + structural finiteness |
| 11 | **#477** | `erdos_477.X_pow_three` | S7 | 7 | 6 | 10 | explicit-witness | Sekanina-Erdős: NO `A⊂ℤ` and exact-once representation `z=a+b³`. AlphaProof already solved deg-2 variant. Natural next |
| 12 | **#477** | `erdos_477.monomial` | S7 | 7 | 6 | 10 | explicit-witness | Same for `X^k`, all k≥2 — uniform conjecture |
| 13 | **#891** | `erdos_891.variants.weisenberg` | S7 | 7 | 6 | 10 | explicit-witness | Erdős-Weisenberg: ∃ᶠ n s.t. ∀m∈[n, n+(∏p_i)−1], ω(m)≤k |
| 14 | **#944** | `erdos_944` | S6/S7 | 6 | 7 | 10 | graph-witness | Full Erdős 944: for all k≥4, r≥1, ∃ k-critical graph with all critical edge sets >r |
| 15 | **#944** | `erdos_944.variants.dirac_conjecture` | S6/S7 | 6 | 7 | 10 | graph-witness | Dirac general: ∀k≥4, ∃ k-critical graph with no critical edge (k≥5 solved, k=4 open) |

---

## Snipe-Signature Distribution

```
S7 (explicit-witness)              35  (70%)
S1/S5 (bounded + structural)        9  (18%)
S1 (bounded native_decide)          3  ( 6%)
S6 (small graph counterexample)     1  ( 2%)
S6/S7 (graph + witness)             2  ( 4%)
```

**Lane breakdown:**
- `S7-explicit-witness`: 33
- `S1-S5-bounded-or-structural`: 9
- `S6-graph-witness`: 3
- `S1-bounded-or-witness`: 3
- `S7-structural`: 1
- `S7-existential`: 1

The dominant snipe pattern in this long-tail is **S7 explicit-witness construction**: 70% of candidates ask `∃ x, P(x)` where `P` is decidable (often `∀` over a finite type or a coprime-class). This is exactly the slot712 / slot737 / slot739 mechanism Aristotle has already demonstrated.

---

## Domain Distribution

```
nt              35  (70%)
combinatorics   10  (20%)
geometry         2  ( 4%)
algebra          2  ( 4%)
analysis         1  ( 2%)
```

The long-tail is overwhelmingly **number theory** — exactly where Aristotle's S1/S5/S7 DNA has the best fit.

---

## The 5 Most-Promising for Immediate Week 4 Submission

These five are the highest-composite candidates with the lowest competition risk and the most tractable witness structure for the gap-targeting / bare-conjecture pipeline:

### W4-A: Erdős 373 Surányi variant — `n! = a!·b!` complete classification
- **Theorem**: `erdos_373.variants.suranyi`
- **Statement**: `{(n,a,b) : ℕ × ℕ × ℕ | n! = a!·b! ∧ 1<n ∧ 1<a ∧ 1<b ∧ b≤a ∧ a+1≠n} = {(10,7,6)}`
- **Snipe lane**: S1/S5 — bounded native_decide for the equation up to a structural bound (Stirling-driven bound on n), then a structural lemma for n > bound. Surányi 1960s knew only (10,7,6); 60+ years untouched.
- **Why now**: Aristotle's slot618 (Casas-Alvero char-p), slot693 (E850 primeFactors), slot737 (σ₀ multiplicativity) all use the same `bounded check + structural negative case` DNA.
- **Closure-mechanism**: full classification (direction_closure) ✓

### W4-B: Erdős 944 Dirac k=4 — 4-critical graph with no critical edge
- **Theorem**: `erdos_944.dirac_conjecture.k_eq_four`
- **Statement**: `∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1` (Lane: S6)
- **Snipe lane**: S6 — explicit Fintype graph (10-30 vertices). Aristotle's Tuza arc (slots 114/131/250/267) is the proof of concept.
- **Why now**: The Tuza-class DNA is alive; Dirac's k≥5 cases were solved by hand (Brown 1992, Lattanzio 2002, Jensen 2002). k=4 is the only remaining case and demands a SAT-search.
- **Closure-mechanism**: disproof of universal "must have a critical edge" → existence of cex (disproof_closure) ✓
- **Caveat**: `answer(sorry)` in the formal statement — but the substantive theorem (`∃` form) is directly snipe-able if we reformulate the sketch as the existence claim.

### W4-C: Erdős 100 Piepmeyer — 9 points, distance-separated, diameter <5
- **Theorem**: `erdos_100_piepmeyer`
- **Statement**: `∃ A : Finset ℝ², A.card = 9 ∧ DistancesSeparated A ∧ diam (A : Set ℝ²) < 5`
- **Snipe lane**: S7 — pure explicit witness in ℝ². Piepmeyer's published construction is the witness.
- **Why now**: Pure formalization of a known result. The witness is already known; Aristotle just needs to verify `DistancesSeparated` (decidable for finite Finset) and `diam < 5` (compute via `Finset.image` on pairs).
- **Closure-mechanism**: full_closure (formalization_of_solved on a published 9-point witness).

### W4-D: Erdős 477.X_pow_three — Sekanina cubic
- **Theorem**: `erdos_477.X_pow_three`
- **Statement**: `∀ A : Set ℤ, ∃ z, ¬ ∃! a ∈ A ×ˢ (X³.eval '' {n | 0 < n}), z = a.1 + a.2`
- **Snipe lane**: S7 — universal-existential. AlphaProof has already solved the degree-2 variant (`erdos_477.degree_two_dvd_condition_b_ne_zero`); this is the natural cubic extension.
- **Why now**: Direct DNA match to the proven AlphaProof solution. The algebraic technique that worked for X² should generalize.
- **Closure-mechanism**: direction_closure (specific polynomial) ✓

### W4-E: Erdős 324 quintic — `a^5 + b^5` distinct sums
- **Theorem**: `erdos_324.variant.quintic`
- **Statement**: `{(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => a^5 + b^5`
- **Snipe lane**: S1 — universal `∀ (a,b)≠(c,d), a^5+b^5 ≠ c^5+d^5` over a bounded scope. With explicit bound (no `a, b, c, d` < N produces a collision), `native_decide` settles it. Then extend via Faltings-style or elementary divisibility.
- **Why now**: Pure number-theoretic decidable claim. Long open (Erdős 1948), low forum activity (2 comments, no AI claims), and high Aristotle-fit.
- **Closure-mechanism**: full_closure for bounded case → structural argument for large case.

---

## The Single Most Surprising "This Should Have Been Done Already" Candidate

**Erdős 100 Piepmeyer (`erdos_100_piepmeyer`)**

The conjecture asks: ∃ a Finset of 9 points in ℝ² with all pairwise distances separated by ≥1 (when distinct) AND with diameter < 5. 

**Piepmeyer's published construction already exists.** This is a literal formalization — a known witness from the 1990s waiting for a 30-line Lean encoding. Distance verification is decidable (rational distances → `decide`). Yet:
- Zero forum comments on erdosproblems.com/100
- Zero prior Aristotle attempts
- Zero AI-team flags in the wiki AI-contributions audit
- Aristotle slot740 already demonstrated the exact DNA: greedy + CRT + `native_decide` on finite grids — same mechanism

The published Piepmeyer construction has been sitting in the literature for ~30 years. Aristotle should be able to convert it to Lean in a single sketch.

**Honorable mention** for "surprising":
- **Erdős 373 Surányi** — the conjecture that `n! = a!·b!` has only `(10!, 7!·6!)` as a solution has been open since the 1960s with zero forum traffic and zero AI attempts. The mathematics has clear S1/S5 structure: bounded check (Stirling) + structural multiplicativity argument. 60-year-old conjecture that's never had a serious computational push.

---

## Documentation

- **Candidates CSV**: `/Users/patrickkavanagh/math/analysis/long_tail_erdos_candidates.csv` (50 ranked candidates, full columns)
- **This summary**: `/Users/patrickkavanagh/math/analysis/long_tail_erdos_summary.md`
- **Source data**:
  - Registry: `/Users/patrickkavanagh/math/analysis/open_problems_registry_may30.csv`
  - Kill list: `/Users/patrickkavanagh/math/analysis/literature_kill_list.csv`
  - Competition audit: `/Users/patrickkavanagh/math/analysis/ai_competition_audit_may30.csv`
  - DNA: `/Users/patrickkavanagh/math/analysis/advance_dna_may30.md`
  - Closure list: `/Users/patrickkavanagh/math/analysis/closure_list_may30.md`

---

## Cautions

1. **`answer(sorry)` penalty**: 28 of 50 candidates contain `answer(sorry) ↔ ...`. Submitting these requires first establishing the answer (true/false/value). The `.variants.*` and `.parts.*` form (without `answer(sorry)`) is usually directly target-able.
2. **AI competition flags**: Erdős 477 (AlphaProof on degree-2 variant), Erdős 730 (AlphaProof, same prime divisors), Erdős 939 (GPT lit search), Erdős 949 (AlphaProof partial), Erdős 513/951 (GPT). These are competition-aware: still open but AI is watching.
3. **Bloom caveat (per registry summary)**: erdosproblems.com 'open' means "Bloom is unaware of a paper resolving it." Some candidates may have classical resolutions outside the AI corpus — always check Bloom's references before submitting.
4. **`finite_compute_disallowed` flag**: 4 candidates (#1055, #1065a, #680, others) have erdosproblems.com text "cannot be resolved with a finite computation" — these are still snipe-able via S7 but need an *infinite*-witness construction, not just a finite check.
5. **`.variants.parallelogram` (E189)**, `.variants.suranyi` (E373), `.dirac_conjecture.k_eq_four` (E944) and similar — the formal-conjectures repo distinguishes the main `answer(sorry)` form from the named sub-conjectures. **Submit the sub-conjecture form** (no answer-sorry), not the main form.
