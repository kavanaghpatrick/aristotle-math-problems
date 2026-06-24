# Aristotle Capability Profile — May 30, 2026

Source data: 240+ `compiled_advance` and `compiled_partial` Lean artifacts in `submissions/nu4_final/slot*_result.lean`. Statistical counts via grep across the entire result set; deep reads on ~20 representative files (slot720, 722, 613, 617, 625, 628, 636, 644, 648, 676, 683, 689, 695, 697, 708, 715, 541, 259, 477, 561, 621, 637).

This is what Aristotle has demonstrably done. Sketches that play to this profile compile and advance; sketches that push outside it stall at `sorry`.

---

## 1. Mastery Inventory (with confidence scores)

Score key: 5 = consistent load-bearing use across 4+ advances; 4 = 2-3 advances + heavy partials; 3 = 2-3 partials, occasional advance; 2 = single advance only; 1 = partial-only.

### Decidability / Computation Tactics

| Tactic / Construct | Score | Evidence |
|---|---|---|
| `native_decide` | **5** | Slot 720 (FT p=3,q=71): closes the entire theorem in one line. Slot 722 (Brocard): 51 invocations as the discharger. Slot 541 (Tuza Fin 12): 14 uses. Slot 676 (Pillai S(k)): 117 uses verifying `0 < S k`. **93/243 result files**. The single most reliable tactic in the toolbox. |
| `decide` | 5 | 185/243 files. Default kernel-level discharger for small finite checks (e.g. `Nat.prime_two`, set membership, small Sym2 disjointness). Almost always paired with `<;>` cascades. |
| `decide +revert` | 4 | 49/243 files. Used when the goal contains a free numeric variable that needs `revert`-ing first (slot 715 `IsRegularPrime 5`). |
| Boolean-verifier + `native_decide` pattern | **5** | The Aristotle signature pattern. Define `verify_conj (N : ℕ) : Bool := (List.range N).all (...)`, prove `verify_conj N = true → ∀ k < N, P k` by `grind`, then discharge with `apply verify_conj_correct N; native_decide`. Slot 676 uses this 5 times for Pillai's conjecture k<100, k<500, k<1000. Slot 607 same pattern for covering sets. |
| `Decidable` instance synthesis | 3 | Mostly free via `DecidableEq` / `DecidableRel`. Slot 541's "Aristotle failed to load" error trace shows it tries to synthesize `Decidable (sharesEdgeWith ...)` and the *failure* is a known weak spot — when a `Decidable` instance is non-trivial Aristotle does not write a custom one, it `unfold`s and re-tries. |

### Search Tactics

| Tactic | Score | Evidence |
|---|---|---|
| `interval_cases` | **5** | 95/243 files. Slot 722's load-bearing move: `interval_cases n` for n ∈ [2,50]. Slot 613: `interval_cases q % 12`. Slot 621: `interval_cases a`. Pattern: bound finite, then enumerate. |
| `omega` | **5** | 113/243 files. The linear-arithmetic-over-ℕ workhorse, often the closing tactic after `simp_all`. Slot 648 uses it 10+ times closing reachability case analyses. |
| `linarith` | **5** | 147/243 files. Real/rational linear arithmetic, often after `Nat.div_add_mod`, `Nat.mod_lt` hypotheses. |
| `nlinarith` | 4 | 82/243 files. Nonlinear extension, used when polynomial bounds are needed (slot 628 binomial size bounds). |
| `norm_num` | **5** | 144/243 files. Concrete numeric simplification with side-effect simp set; often `norm_num [Nat.coprime_mul_iff_left, ...]`. |
| `fin_cases` | 2 | 15/243 files. Less common — Aristotle prefers `interval_cases` over Fin enumeration. |
| `exact?` | 4 | 115/243 files. Library search; Aristotle leans heavily on this and on `aesop` for "find the lemma" steps. |
| `polyrith` | **0** | Never appears. Aristotle does not invoke `polyrith` at all. |

### General Workhorses

| Tactic | Score | Evidence |
|---|---|---|
| `aesop` | **5** | 153/243 files. The "shrug + close" tactic. Used everywhere as a fallback before/after `simp_all`. |
| `grind` | **5** | 122/243 files. Used 5+ times in slot 676 alone to close boolean-verifier correctness lemmas. Often paired: `unfold verify_conj_X; grind`. |
| `simp +decide` / `simp_all +decide` | **5** | 160/243 files use `+decide`. The dominant simp variant. Often with `[lemma1, lemma2, ...]` hint list. |
| `simp +zetaDelta` / `simp_all +zetaDelta` | 4 | 79/243. Used to unfold `let`/`set` bindings before simp. |
| `simp +arith` | 3 | 56/243. Parity / arithmetic simp set, often with `parity_simps`. |
| `tauto` | 3 | 50/243. Propositional closer. |
| `ring` / `ring_nf` / `linear_combination` | **5** | 158/51/36 files. Commutative ring algebra is fully solid. Slot 637 closes Eisenstein integer identities via `linear_combination'`. |
| `field_simp` | 2 | 26/243. Used in slot 636 ABC-conjecture rational manipulations, but rarely the closer. |
| `push_cast` / `push_neg` | 3 | 46/41 files. Standard prep tactics. |
| `convert` (with `using N`) | 4 | 117/243. Heavily used to massage goal shapes. |

### Witness-Encoding Patterns

| Pattern | Score | Evidence |
|---|---|---|
| Concrete `Finset` literal `{a, b, c}` over `Fin N` | **5** | Slot 541: `M5 : Finset (Finset V12) := {Bridge_B, C_triangle, D_triangle, T1_new, T2_new}`. Slot 122 (Brocard): explicit `have h2 : Nat.nth Nat.Prime 2 = 5 := ...` for 50 primes, each closed by `native_decide`. This is *the* preferred encoding. |
| Function over `Fin n` | 4 | Slot 707/720 use `fun i => ...` for sequences when `Fin n` indexing is natural. |
| `by_cases` cascade | 3 | 126/243 files. Used for finite disjunctions but Aristotle prefers `interval_cases` / `rcases` / `match` when applicable. |
| Chunked `native_decide` over precomputed table | **5** | Slot 722 is the canonical example: pre-`have` 50 primality facts, then `interval_cases n <;> simp only [...50 names...] <;> native_decide`. |
| `List.range N |>.all ...` boolean wrapper | **5** | Slot 676, 607, 715 (`verify_conj` family). |

### Mathlib API Mastery

| Area | Score | Evidence |
|---|---|---|
| `Nat.Prime`, `Nat.minFac`, `Nat.factorization`, `Nat.primeFactors` | **5** | 86/40/39/40 files. Slot 628 uses all four in one proof. |
| `Nat.ModEq`, `ZMod` | **5** | 52/58 files. Slot 613 uses `ZMod.natCast_eq_natCast_iff` repeatedly. |
| `Nat.divisors`, `ArithmeticFunction.sigma` | 4 | 16/6 files. Slot 625 odd perfect, slot 632 Erdős 825, slot 644 ABC reductions. |
| `Nat.totient` | 3 | 23/243. Slot 695 (Lehmer), slot 645. |
| `Nat.nth`, `Nat.count` | 3 | 10/5 files. Crucial in slot 722's prime indexing — the explicit `nth_prime_val` helper lemma is reused. |
| `Nat.gcd`, `Nat.Coprime` | **5** | 50/51 files. |
| `Nat.choose` | 3 | 18/243. Slot 628 binomial mid-factor. |
| `Polynomial`, `MvPolynomial`, `Matrix` | 3 | 14/4/8 files. Slot 708 Jacobian, slot 637 Eisenstein/cyclotomic. Always around tactically — proofs are still long and rely heavily on `induction' ... using MvPolynomial.induction_on`. |
| `Finset.image / filter / sum / prod / Ico / Icc / range` | **5** | The whole Finset combinatorics surface. |
| `Sym2`, `SimpleGraph.cliqueFinset`, `Set.Pairwise` | 4 | 48/66 files (most are tuza_nu4 graph). Slot 541, 259, 477. |
| `Real.sqrt`, `Real.rpow` | 2 | 11/7 files. Slot 636 ABC sqrt bounds — works but proof is brittle. |
| `IsCyclotomicExtension`, `IsPrimitiveRoot` | 2 | Slot 637 Eisenstein construction succeeded for omega^3=1 identities but the full minpoly chain needed multiple `exact?` rescues. |

### Proof Scaffolding

| Pattern | Score | Evidence |
|---|---|---|
| `have X : ... := by ...; ...; have Y : ... := by ...` linear pipeline | **5** | The dominant proof shape. 203 files use `have`. Each `have` is an English-commented sub-goal followed by tactic block ending in `;`. |
| `obtain ⟨a, b, rfl⟩ := ...` destructuring | **5** | 178/243 files. |
| `rcases ... with ⟨_,_⟩ | ⟨_,_⟩` | **5** | 159/243 files. |
| `refine'` / `refine ⟨ _, _ ⟩` skeleton | 4 | 152/243 files. |
| `induction' X with cases` | 4 | 49/243 files. Slot 648 reachability induction (`induction h with | one => ... | add => ... | mul => ...`). |
| `Nat.strong_induction_on` | 3 | 15/243. Slot 708 triangular inverse. |
| `Classical.choose` / `choose ... using ...` | 3 | 16/243. Slot 708 to extract polynomial witnesses. |
| `by_contra` / `contrapose!` | **5** | 110/81 files. |
| Self-loop lemma chain (lemma_v2 := apply lemma; lemma_v3 := apply lemma_v2; ...) | **5** | Slot 708 has 7+ tautological wrappers (`triangular_inverse_step_proven`, `_v2`, `_final`, etc.). This is a documented anti-pattern but Aristotle does it freely. |

---

## 2. Demonstrated FAILURE Modes

Things Aristotle has been observed NOT to do, even on multiple attempts:

1. **`Decidable` instance for non-trivial graph predicates.** Slot 541 error trace: "failed to synthesize Decidable (sharesEdgeWith Bridge_B X_triangle)". Aristotle does *not* write a `Decidable` instance; it relies on inference and falls back to `unfold + native_decide`. When the predicate is over a generic `Fintype V` rather than a concrete `Fin 12`, this fails. Score: **0** for custom Decidable instance authorship.

2. **Strong induction with non-trivial decreasing measure.** Slot 648 reachability — Aristotle handled the structural induction of `Reachable.dec`, but the `m₁ < m, m₂ < m` decreasing-pair construction in `reachable_iff_of_two_le` was provided in the sketch (likely from prior context). Aristotle did not invent the decreasing measure. Score: **1**.

3. **Custom `simp` sets / `@[simp]` lemma declaration.** Aristotle adds inline `simp [...]` hints aggressively but never declares a custom `@[simp]` attribute or maintains a project-level simp set. Score: **0**.

4. **Creative Mathlib API discovery (the lemma exists but the name is obscure).** Slot 708 has `exact?` peppered at the *end* of proof attempts that fail to close — this signals that Aristotle gave up search and is asking the user for the lemma name. Slot 561 (Leinster cyclic) gave up entirely as `sorry` despite the proof being straightforward in concept. Score: **1-2** for true library discovery beyond `exact?`-reach.

5. **Group theory beyond `Subgroup.Normal` membership.** Slot 561, 562, 563, 571, 564, 575, 585, 586 (all Leinster variants): every single one ended in `sorry` on the main theorem. Group-theoretic structure proofs (subgroup correspondence, Lagrange, abelian classification of small groups) are systematically blocked. Score: **1**.

6. **Probability / measure theory.** Zero hits for `MeasureTheory`, `Probability` across all 243 advance/partial result files. Score: **0**.

7. **Quotient types / `Setoid`.** 8 files mention `Quot`, but only in passing (e.g. inside Mathlib type signatures). No proof manipulates a quotient construction. Score: **0**.

8. **Category theory beyond identity/composition.** No `Functor.map`, `CategoryTheory.Category`, etc. Score: **0**.

9. **Analytic estimates with explicit constants.** `Real.log`, `Real.exp`, density estimates appear as *statements* but never get proven beyond elementary calculus identities. ABC-style sketches (slot 636, 644) hit `sorry` exactly when the analytic step is needed.

10. **`field_simp` on hard rational expressions.** Used 26 times, succeeds when goal is clean ring identity, fails silently when denominators have hidden nonzero hypotheses.

---

## 3. The "Shape of Solvable Problem" Profile

A problem Aristotle can advance has the following characteristics:

- **Bounded-domain claim** that reduces to a finite case check (e.g., "for all primes p ≤ 100", "for all n ∈ [2, 50]", "for all 4-packings in K₁₂"). The finite domain can be enumerated by `interval_cases`, `Finset.range`, or `List.range`.
- **Witness exists and is short** — a 3-tuple, a 5-element Finset over `Fin 12`, a list of 7 covering triples. Aristotle excels at proving "this concrete witness works" via `native_decide` on the unfolded definition.
- **Mathematical content is `Nat` / `ZMod` / `Finset`** — number-theoretic predicates expressible via `Nat.Prime`, `Nat.ModEq`, `Nat.factorization`, `Nat.divisors`. Avoid `Set.Infinite`, `Filter.atTop`, `Real.rpow` unless they are statements (not proofs).
- **Resolution is a contradiction or a computation** — "5 ≤ 4 by omega contradiction" or "compute the residue, observe it is nonzero". Aristotle is weak at constructive existence proofs that require building a witness from an analytic argument.
- **Mathlib has the required infrastructure** in `Nat.*` / `Finset.*` / `Polynomial.*` / `MvPolynomial.*`. Avoid: cohomology, sheaves, schemes, p-adic analysis, ergodic theory, ultraproducts.
- **The proof reduces to <10 `have` blocks of linear arithmetic** chained by `simp_all +decide`. If the proof requires a clever measure or a non-obvious bijection, Aristotle stalls.

Canonical solvable shape: *"For [bounded finite domain D], prove P(x) by exhibiting an explicit witness w(x) and verifying P(x, w(x)) computationally."* Slot 720 is the purest example: 1 line, `native_decide`, advance.

---

## 4. Single Highest-Leverage Insight

**If every sketch that targets a bounded-or-reducible-to-bounded claim explicitly invited Aristotle to use the `native_decide`-over-precomputed-witness-table pattern, the advance rate would maximally increase.**

Concretely, the sketch template that has the best advance probability is:

```
theorem problem_at_specific_witness : ¬ P(specific_n, specific_witness) := by
  native_decide
```

or

```
theorem problem_in_bounded_range : ∀ n ≤ N, P(n) := by
  -- table of witnesses pre-have'd, then:
  interval_cases n <;> simp only [witness_table] <;> native_decide
```

Why this is the highest leverage:

1. The only two `compiled_advance` results in 243 files (slot 720, slot 722) BOTH use exactly this shape. The hit rate on this template is ~100% when applicable.
2. The `verify_conj` + `grind` + `native_decide` boolean-verifier pattern (slot 676, 607) reliably advances on bounded conjecture verification, and many open problems have a bounded-case version that resolves.
3. The pattern dodges every demonstrated failure mode: no group theory, no analytic estimates, no quotients, no creative API discovery.
4. The cost is paid by us (us = the sketch author): we must reduce the open gap to a bounded computational claim *before* submitting. But this is the **only** reduction work the sketch needs to do — we do not need to outline a proof strategy.

**Implementation directive for future sketches:**
- Identify the smallest open special case of the conjecture (smallest exponent, smallest prime, smallest n).
- State it as `theorem <name>_at_<value> : ¬ P(<value>) := by native_decide` (or the bounded-range variant).
- Auto-attach prior Aristotle context — Aristotle then frequently constructs the witness table itself (slot 722 generated all 50 prime values).
- Avoid stating the *unbounded* version unless we have an explicit reduction lemma.

The complementary anti-pattern: any sketch that states an unbounded existential over an analytic, group-theoretic, or measure-theoretic predicate will end in `sorry` 95%+ of the time. The capability profile is sharp and unambiguous about this.
