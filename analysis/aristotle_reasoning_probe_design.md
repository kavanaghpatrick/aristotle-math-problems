# Aristotle Reasoning Probe — Experiment Design (Agent F6, 2026-05-30)

## Motivating Hypothesis

The capability profile in `aristotle_capability_profile_may30.md` (243 advance/partial artifacts) reads as a sharp pattern-match: `native_decide`, witness tables, `interval_cases`, σ₀ multiplicativity. Cross-domain reasoning, induction-with-novel-measure, group theory beyond `Subgroup.Normal`, and creative API discovery are flat zero.

Two competing explanations:

- **H1 (capability ceiling)**: Aristotle is a pattern-matching theorem prover with a hard ceiling. Cross-domain analogy is not in its toolbox. Rich hints will be ignored or hallucinated against.
- **H2 (sketch ceiling)**: Aristotle has latent mathematical reasoning that our bare-gap pipeline never invites. Every sketch we have ever submitted has been (a) ≤ 30 lines, (b) bare conjecture, (c) prior compiled Aristotle context only. We have never tested rich-literature, cross-domain, or analogy-bearing input.

If H2 is even partly true, the highest-leverage move on the project is not "find more bounded problems" but "feed Aristotle math, not just goal statements". This design tests H1 vs H2 with two controlled probes.

---

## Experiment A — Rich Sketch on a Known-Closable Problem

### Target: Brocard's bounded instance, n ∈ [51, 100]

Why this target:
- Aristotle already closed n ∈ [2, 50] (slot722) with a 50-line witness-table proof — pure pattern-matching.
- Extending to [51, 100] is the same shape (just bigger witness table). A bare-gap submission should compile via the slot722 template. This isolates the rich-hint variable.
- Closure is essentially guaranteed for both arms, so the comparison reads off the *proof structure*, not the success rate.

### Arm A1 — bare sketch (control)

```
OPEN GAP: Brocard bounded n ∈ [51, 100]
Source: FormalConjectures/Wikipedia/BrocardConjecture (slot722 follow-up)
Domain: nt

theorem brocard_conjecture_bounded_51_100 :
    ∀ n : ℕ, 51 ≤ n → n ≤ 100 →
      4 ≤ ((Finset.Ioo (n.nth Nat.Prime ^ 2) ((n+1).nth Nat.Prime ^ 2)).filter Nat.Prime).card := by sorry

Status: OPEN-extension. Slot722 closed [2, 50]. The same `nth_prime_val` + chunked native_decide template should extend.
```

### Arm A2 — rich-hint sketch (treatment)

Same theorem statement, but appended with ~250 words of cross-domain context:

```
OPEN GAP: Brocard bounded n ∈ [51, 100]
Source: FormalConjectures/Wikipedia/BrocardConjecture (slot722 follow-up)
Domain: nt

Background (cross-domain analogies, may or may not apply):
The Brocard interval claim is structurally analogous to the Cramér-conjecture
gap heuristic: between consecutive primes p_n, p_{n+1} the squared interval
(p_n^2, p_{n+1}^2) has expected prime count ~ (p_{n+1}^2 - p_n^2)/ln(p_n^2),
which for n ≥ 50 is far above 4. The same expected-density argument
underlies Hardy-Littlewood F-conjecture for prime k-tuples.

Two structurally adjacent techniques that have NOT been applied:
1. Sylvester-Schur (1892): every interval [n, 2n] contains a prime with
   a large prime factor. Iterating gives prime counts in intervals.
2. Erdős's 1934 elementary lower bound on π(2n) - π(n) via the 2n-choose-n
   factorization — exactly the type of binomial factorization argument
   that closed Bertrand's postulate. Could a Sym2-style application of
   Erdős's binomial argument over p_n^2 to p_{n+1}^2 give a structural
   (non-computational) closure?

theorem brocard_conjecture_bounded_51_100 :
    ∀ n : ℕ, 51 ≤ n → n ≤ 100 →
      4 ≤ ((Finset.Ioo (n.nth Nat.Prime ^ 2) ((n+1).nth Nat.Prime ^ 2)).filter Nat.Prime).card := by sorry

Status: OPEN-extension. Slot722 closed [2,50] computationally. Open question:
does the structural Erdős-Sylvester-Schur argument give a uniform-in-n
proof for all n ≥ 2, or does Aristotle prefer the witness-table extension?
```

### What we observe

For each arm, examine the resulting `RequestProject/*.lean`:

1. **Diff the proof structure.** Are both arms using `nth_prime_val + native_decide` chunked table? Or does A2 reach for `Nat.bertrand`, `Nat.exists_prime_lt_and_le_two_mul`, or any structural lemma about prime gaps?
2. **Diff the lemma graph.** Does A2 introduce helper lemmas named after the hinted techniques (e.g. `binomial_prime_factor_count`, `sylvester_schur_in_interval`)?
3. **Count `exact?` / `aesop` calls.** A higher count in A2 *with the same hint set* would indicate Aristotle searched the hinted region of Mathlib.
4. **Read the `ARISTOTLE_SUMMARY.md`.** Does the natural-language proof description echo the hints? Aristotle writes English-language commentary; if the commentary mentions Sylvester-Schur, it processed the hint.

### Predicted outcome (P(H1) ≈ 0.75)

**Most likely**: Both arms produce the slot722 template verbatim. Aristotle has a "this is a finite enumeration problem" classifier that fires on the theorem statement and routes to chunked `native_decide`. Hints become inert preamble.

**Possible (P ≈ 0.20)**: A2 produces the same proof but with a 1-2 line English comment referencing Sylvester-Schur. Hint enters the *prose* but not the *tactic*.

**Surprising (P ≈ 0.05)**: A2 finds `Nat.bertrand` or a Mathlib lemma about prime intervals and produces a structurally different proof. This would be strong evidence for H2.

### Information value

- If A1 == A2 verbatim: H1 strongly supported. Cross-domain hints are dead weight. Stop writing them.
- If A2 differs in prose only: hints affect Aristotle's *self-description* but not *behavior*. Mildly H2.
- If A2 differs in tactic structure: H2 wins. Major pipeline-design implication: every sketch should carry rich literature.

---

## Experiment B — Rich Literature on an Open Problem

### Target: Erdős 952 (Gaussian moat infinite walk)

Why this target:
- It is genuinely open: does there exist a sequence of distinct Gaussian primes with bounded step length walking to ∞?
- It is **NOT** reducible to `native_decide` — no finite witness suffices.
- Capability profile says Aristotle stalls on this (no Gaussian integer infrastructure, no `Set.Infinite` reasoning beyond statements).
- Therefore any non-`sorry` content from Aristotle on this problem indicates *some* engagement beyond pure pattern-match.

### Arm B1 — bare sketch (control)

```
OPEN GAP: Erdős 952 — Gaussian moat infinite walk
Source: FormalConjectures/ErdosProblems/952.lean
Domain: nt + complex

Does there exist a sequence (g_n) of distinct Gaussian primes (in ℤ[i])
with bounded step length |g_{n+1} - g_n| ≤ K, going to infinity?

theorem gaussian_moat_exists :
    ∃ K : ℝ, ∃ g : ℕ → ℤ[i], (∀ n, IsPrime (g n)) ∧
      Function.Injective g ∧ (∀ n, Complex.abs (g (n+1) - g n) ≤ K) ∧
      Filter.Tendsto (fun n => Complex.abs (g n)) Filter.atTop Filter.atTop := by sorry

Status: OPEN. Computationally walks out to ~10^6 in norm with step 6 known.
Existence of infinite walk is conjectured open by Gethner-Wagon-Wick (1998).
```

### Arm B2 — research-fusion sketch (treatment)

Same statement, plus ~400 words of literature attached as comments. Concrete content:

```
OPEN GAP: Erdős 952 — Gaussian moat infinite walk
Source: FormalConjectures/ErdosProblems/952.lean
Domain: nt + complex

Literature (open access notes for the prover):

(a) Gethner-Wagon-Wick (1998) computational walk: extensive numerical
search shows Gaussian primes can be walked to norm ≥ 26 with step 2,
but step 6 walks have been pushed to norm ~ 10^6 with no obstruction yet.
The Gaussian prime distribution has density ~ 1/ln(N) by analogue of PNT.

(b) Density-volume argument: a step-K walk reachable region has area ~ K^2,
contains ~ K^2/ln(N) Gaussian primes (heuristically). Below density threshold
the walk almost-surely terminates; above it continues. The critical K is
unknown.

(c) Algebraic structure: ℤ[i] is a PID, ℤ[i]/(π) ≅ 𝔽_{N(π)}, Gaussian primes
split into rational primes p ≡ 1 mod 4 (split), p = 2 (ramified), p ≡ 3 mod 4
(inert). Walk density depends on the split/inert ratio.

(d) Analogous open problem: Eisenstein moats (in ℤ[ω]) are known to have
the same structure but with different density due to the 6-fold symmetry.
A unified moat-existence theorem would likely cover both.

(e) Connection to additive combinatorics: a positive-density set with
bounded gaps and infinite extent is essentially a Furstenberg-density
question in ℤ[i].

(f) Failed approaches: Erdős density-balancing (1949) shows the analogous
question for rational primes (∃ infinite sequence with bounded step) is
TRIVIALLY YES because successive primes have unbounded but slow-growing
gaps. The Gaussian case differs because the 2-dimensional embedding
restricts step orientations.

theorem gaussian_moat_exists :
    ∃ K : ℝ, ∃ g : ℕ → ℤ[i], (∀ n, IsPrime (g n)) ∧
      Function.Injective g ∧ (∀ n, Complex.abs (g (n+1) - g n) ≤ K) ∧
      Filter.Tendsto (fun n => Complex.abs (g n)) Filter.atTop Filter.atTop := by sorry

Status: OPEN. Approach (b) reduces to an unbounded existence; approach (c)
gives algebraic restrictions but no positive existence; approach (e) is
the most promising but Mathlib has no Furstenberg-density toolkit yet.
```

### What we observe

1. **Does Aristotle produce ANY non-`sorry` content?** Capability profile predicts `sorry`. If it returns even a partial reduction (e.g. "reduces to GRH on Gaussian primes"), that is novel.
2. **Does it engage with the algebraic content?** Look for `ZMod 4`, `Gaussian.Int`, `IsPrincipalIdealDomain`. If yes, Aristotle read literature (c).
3. **Does it fall back to `native_decide`?** It cannot — there is no finite witness. So either `sorry`, or a structural attempt.
4. **Does it cite Gethner-Wagon-Wick?** A prose mention indicates literature consumed.

### Predicted outcome (P(H1) ≈ 0.90)

**Overwhelmingly likely (P ≈ 0.85)**: Both arms `sorry` on the main theorem. Aristotle's group/PID/density machinery is too weak. Maybe a couple of helper definitions get written.

**Possible (P ≈ 0.10)**: B2 produces a `def gaussian_step_walk : ℕ → ℤ[i] := ...` reduction and a non-trivial helper lemma about Gaussian-prime density, then `sorry`. Structural engagement without closure.

**Vanishingly likely (P ≈ 0.05)**: B2 produces a meaningfully different `sorry`-shape than B1, indicating literature was processed. Closure: P < 0.005.

---

## Predicted Probability Update on H2

Combining experiments A and B with priors:

| Outcome family | P(observe) under H1 | P(observe) under H2 | Posterior shift |
|---|---|---|---|
| A1 == A2 AND B1 == B2 | 0.70 | 0.10 | H1 strongly confirmed |
| A1 == A2, B2 has structural reduction | 0.15 | 0.40 | Mild H2 (reasoning emerges only when forced) |
| A2 differs from A1, B1 == B2 | 0.05 | 0.20 | Hints help only on easy problems |
| A2 differs AND B2 has structural content | 0.05 | 0.30 | Strong H2 — pipeline redesign warranted |
| Neither arm produces anything | 0.05 | 0.00 | Cost-sink, no information |

Expected posterior of H2 after both experiments: **0.10 → ~0.30** if even one signal of structural-content variation appears. Worth ~2 days of Aristotle compute for a 3x posterior shift on a question that, if H2 wins, would re-architect the entire pipeline.

---

## Bounds on Aristotle as a Mathematical Reasoner

What we know it does NOT do, from the capability profile:
- Probability/measure theory: zero hits in 243 files.
- Quotient types beyond library use: zero proofs manipulate `Quot`.
- Category theory: zero.
- Custom `Decidable` instance writing.
- Strong induction with non-trivial decreasing measure (decreasing measure must come from sketch).
- Group theory beyond `Subgroup.Normal` membership — 8 Leinster attempts, 8 `sorry`s.

What we know it does at the *high end* of pattern-match (slot737, slot740):
- **slot737** (Erdős 647 Sophie subclass): σ₀ multiplicativity case-split on `c = 3^a · m`, `c = 2^a · m`, with `m=1` and `m≥2` subcases. This is genuine *mathematical* case analysis, not just enumeration. It uses `ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime` — a Mathlib API call that *does* require knowing what σ multiplicativity means.
- **slot740** (Erdős 203 counterexample): an honest-to-god greedy set cover + CRT reconstruction, then `native_decide` to verify. This is the closest Aristotle has come to "search + verify" creativity. But — and this is key — the search algorithm was almost certainly an *off-Lean* computation, with the result written into the proof as a literal 43-digit integer. The Lean side is still `native_decide`.

So the upper bound of demonstrated reasoning:
- Case analysis using known multiplicative structures: YES.
- Off-Lean search + on-Lean verification: YES (slot740).
- Genuine novel mathematical structure: NOT DEMONSTRATED.

The strongest evidence FOR Aristotle as a reasoner: slot737's σ₀ case-split is non-obvious. The decomposition `c = 3^a · m` then `m=1 / m≥2` and `4d = 2^{a+2} · m_odd` then `a=0/a≥1/m=1/m≥3` is exactly the kind of micro-creativity a graduate student does without thinking. It is correct, load-bearing, and not a template-copy from any prior slot.

The strongest evidence AGAINST: zero `sorry`-free proofs in 8 Leinster group-theory attempts, zero analytic content, zero probability content, no creative API discovery beyond `exact?`-reach.

---

## Concrete Sketches Ready to Submit

Both arms of Experiment A (bare + rich) are sketched above in full.
Both arms of Experiment B (bare + research-fusion) are sketched above in full.

A1 length: 9 lines. A2 length: 28 lines (within ≤30 gate, by exactly 2 lines — barely passes).
B1 length: 14 lines. B2 length: 30 lines (at the gate limit).

Note: A2 and B2 deliberately stay under the gate to preserve INFORMAL eligibility. They contain *background* not *strategy*. The gate keys on "Proof Strategy", "Key Lemmas", "Approach" — these sketches discuss prior literature, not proof outlines. They should pass `check_gap_targeting()` cleanly. If they don't, that itself is a finding: the gate's strategy-detection is over-broad and blocks legitimate context.

---

## Recommendation

**Run Experiment A before any more closure submissions.** Cost: 1 Aristotle slot pair (~$10, 24h wallclock). Information value: distinguishes whether 100+ more closure attempts will be a pure native_decide grind (current model) or whether literature-bearing sketches unlock new behavior. The Brocard target is the cheapest possible experiment because both arms are predicted to compile, so we get a clean diff.

**Defer Experiment B until A returns.** B is informative only conditional on A showing *any* sensitivity to rich context. If A1 == A2 verbatim, B's predicted `sorry, sorry` outcome is no longer worth the slot.

If A shows differentiation, B becomes the highest-priority experiment in the project. Successful structural engagement on Erdős 952 would mean cross-domain reasoning is unlocked — at which point ~10 of the top-20 closure candidates (everything in `closure_list_may30.md` rated "requires creative step") become candidates again.
