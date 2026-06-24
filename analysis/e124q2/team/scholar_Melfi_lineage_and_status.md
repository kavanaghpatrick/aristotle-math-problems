# Melfi lineage, the "amended conjecture", and the exact status of Q2 (finite case)

**Author:** scholar. **Sources (all PDFs retrieved & read):**
- Melfi 2004, "On certain positive integer sequences", arXiv:math/0404555 (7 pp).
- Hasler–Melfi 2024, "On sums of distinct powers of 3 and 4", Comb. Number Theory **13**(2),
  MSP, received 21 Jan 2024, published 1 Jul 2024 (abstract read; full PDF behind MSP).
- Melfi 2001, "An additive problem about powers of fixed integers", Rend. Circ. Mat. Palermo
  (II) **50** (2001), 239–246 [= ref [12] in Melfi04; the n_k ≪ k^1.0353 source].
- Sprague, "Über Zerlegungen in n-te Potenzen mit lauter verschiedenen Grundzahlen" (sums of
  distinct n-th powers cover all large integers) [= ref [18] in Melfi04].

---

## 1. ★ DECISIVE FOR Q2: the BEGL conjecture for FINITE A is genuinely open; only the
##   INFINITE version was disproven. Our Lean Q2 (finite D) is NOT threatened by Melfi.

Melfi 2004 §4 quotes the BEGL conjecture verbatim and then writes (verbatim):

> "As Graham noted [7] [R. Graham, personal communication, 2004], **A must be intended as
> finite**, even if from the text of the conjecture this is not explicitly said. In fact the
> following proposition disproves the conjecture in the case [where] infiniteness is allowed.
> We provide counterexamples using suitable infinite sets A. **However, we point out that for
> finite sets the problem is open.**"

So the historical record is crystal clear:
- **Infinite A:** BEGL conjecture is FALSE (Melfi 2004, Proposition 1, see §2 below).
- **Finite A (= our D):** OPEN. This is EXACTLY our Q2. Melfi did not touch it.

> **TEAM (false-trail kill):** Anyone who finds "Melfi disproved the BEGL conjecture" must NOT
> conclude Q2 is dead. Melfi disproved only the (never-intended) infinite-set reading. Our Lean
> `erdos124.ne_zero` uses `D : Finset ℕ` — finite by construction — so it is the genuinely open
> finite case. Graham himself clarified (2004) the conjecture was always meant for finite A.

## 2. Melfi 2004, Proposition 1 (the infinite counterexample — proof mechanism)

> **Prop 1 (Melfi04).** For every ε ≥ 0 there is an INFINITE set A of integers ≥ 2 with
> (i) ∑_{a∈A} 1/(a−1) < ε, and (ii) for every s ≥ 1, Pow(A;s) is complete.

(I.e. completeness with arbitrarily SMALL harmonic sum — violating BEGL necessity (i) if A may
be infinite. This is the `erdos124.melfi_construction` lemma in our Lean file, ε-thin completeness.)

**Proof mechanism (clean, reusable idea):** pick a prime p ≥ 3. Let `R_p := {n²p : n ∈ ℕ}`.
Then `Pow(R_p; s) ⊇ {n^{2s} p^s}`, and by **Sprague's theorem [18]** (every sufficiently large
integer is a sum of distinct 2s-th powers) one gets `Σ(Pow(R_p;s)) ⊇ {n p^s : n > r}` — i.e. all
large multiples of `p^s`. Then adjoin `Q_p := {p+1}`: since `(p+1)^t` hits infinitely many
residues `≡ 1 (mod p^s)`, `Σ(Pow(Q_p;s))` meets every residue class mod `p^s`. Minkowski-summing,
`Σ(Pow(R_p ∪ Q_p; s))` = (all large multiples of p^s) + (a full residue system mod p^s) = all
large integers. And `∑ 1/(a−1) = 1/p + ∑_n 1/(n²p − 1) < ε` for large p. ∎

> **STRUCTURE WORTH STEALING (for sumset, modular, carry):** this is the cleanest possible
> "ray + residue-filler" completeness template: ONE thick arithmetic ray (all large multiples
> of M) + ONE sparse set that sweeps all residues mod M ⇒ complete. It is the SAME two-part
> decomposition as BEGL96's assembly (Claim 1 gap-filling block + Claim 4 residue sweep). The
> residue sweep again needs a coprimality input: `gcd(p+1, p) = 1` is what makes `(p+1)^t`
> equidistribute mod p^s. This is the micro-version of the gcd condition. For our finite Q2,
> the analogue would be: find within D one base whose powers sweep residues mod (the relevant
> modulus) — but at the harmonic boundary there is no "thick ray" to start from, which is the
> whole difficulty.

## 3. ★ Melfi's Conjecture 1 and the `gcd{A}=1` vs PAIRWISE-coprime subtlety (IMPORTANT caveat)

Melfi04 proposes:

> **Conjecture 1 (Melfi04).** Let s ≥ 1 and A a set of integers ≥ 2. If **for every pair
> a₁,a₂ ∈ A, gcd(a₁,a₂)=1** and `∑_{a∈A} 1/log a > 1/log 2`, then `Σ(Pow(A;s))` has positive
> lower asymptotic density.

He then warns (verbatim): *"if we replace 'for every a₁,a₂∈A, gcd(a₁,a₂)=1' by 'gcd{a∈A}=1' the
statement is NOT true. For the set A = {3, 9, 81, 104}, we have gcd{a∈A}=1, and Σ(Pow(A;s)) has
zero lower asymptotic density [12]."*

**I verified `{3,9,81,104}` numerically:** `∑1/(d−1) = 5333/8240 ≈ 0.647 < 1` (so it is BELOW
the BEGL harmonic threshold and is NOT a BEGL-admissible D — it does NOT contradict our Q2).
Pairwise: gcd(3,9)=3, gcd(9,81)=9 — far from pairwise-coprime; three of the four are powers of 3.

> **WHY THIS MATTERS FOR Q2 (a genuine structural warning):** Melfi's example shows that
> `gcd{D}=1` does NOT by itself prevent a "near-collinear" pathology — if D is dominated by
> powers of a single prime (3, 9, 81) plus a token coprime element, the powers-of-3 bases
> contribute almost nothing new (their B_d's nest: B_9 ⊂ B_3 morally) and density collapses. In
> Melfi's example density is killed by the SUB-CRITICAL harmonic sum (0.647<1), so BEGL's (i) is
> doing the work. BUT it raises the question `density`/`breaker` should test: **does there exist
> a BEGL-admissible D (∑1/(d−1)≥1, gcd{D}=1) that is "prime-power-collinear" enough to fail?**
> If yes, that would be a counterexample to Q2 itself. If the harmonic condition ∑≥1 always
> forces enough "spread" to avoid this, that is the heart of why Q2 should be TRUE. Concretely:
> can you build admissible D where most bases are powers of one prime? E.g. D ⊇ {3,9,27,81,...}.
> ∑1/(d−1) for {3,9,27,81,243} = 1/2+1/8+1/26+1/80+1/242 ≈ 0.667 — STILL < 1, because powers of
> 3 have rapidly shrinking 1/(d−1). **Empirically the harmonic condition seems to FORBID
> prime-power-collinear admissible sets** (powers of p give ∑ 1/(p^j−1) < 1/(p−1) · const < 1
> for p≥3). THIS may be the deep reason Q2 is true — verify rigorously. See §5 below.

## 4. The {3,4} sub-problem line (Melfi 2001 → Hasler–Melfi 2024) — DENSITY, not completeness

`{3,4}` is the BEGL §3 open example. `∑1/(d−1) = 1/2 + 1/3 = 5/6 < 1`, so {3,4} is BELOW the
completeness threshold and `Σ(Pow({3,4}; s))` is NOT complete (has infinitely many gaps). The
question studied is the WEAKER one BEGL posed: does it have positive density? Counting function
`P_{3,4}(x) = #{n ≤ x : n ∈ Σ(Pow({3,4};1))}`.

- **Melfi 2001** [Rend. Circ. Mat. Palermo (II) 50, 239–246]: studies `n_k` = k-th element of
  `Σ(Pow({3,4};1))`; Erdős asked to prove `n_k ≪ k` (⇔ positive density). Melfi proved
  `n_k ≪ k^{1.0353}` (near-linear; ⇔ `P_{3,4}(x) ≫ x^{0.9659}` roughly).
- **Hasler–Melfi 2024** [Comb. Number Theory 13(2)]: improves to `P_{3,4}(x) ≫ x^{0.97777}`,
  plus structural properties. Still does NOT prove positive density (would need exponent 1).
  Erdős's `n_k ≪ k` for {3,4} REMAINS OPEN as of 2024.

> **TEAM NOTE (scope discipline):** the {3,4} line is a DIFFERENT, weaker problem (positive
> density of a sub-critical pair), not our Q2 (completeness of a super-/critical admissible D).
> It is the most ACTIVE research in this neighbourhood (2024!) but it does NOT bear directly on
> Q2's truth. Its relevance: it shows the FIELD'S best tools (Melfi/Hasler) get exponents like
> 0.978 and cannot even close the EASIER {3,4} density question — a sobering calibration on how
> hard the exact completeness Q2 is. This is `density`'s territory; I'm sending them the bounds.

## 5. Synthesis: the precise residual gap and the most promising structural lever

Putting BEGL96 + Melfi together, the state of Q2:
- The two necessity conditions (∑1/(d−1)≥1 [Pomerance], gcd{D}=1 [trivial]) are settled & in
  our Lean file (`converse`, and sumset's gcd-necessity).
- Sufficiency for finite admissible D (= Q2) is OPEN; proven only for the single triple (3,4,7)
  and a handful of small sets, each by ad-hoc Mignotte–Waldschmidt linear-forms computation.
- Melfi shows `gcd{D}=1` is "fragile" (his {3,9,81,104} caution) — but the harmonic condition
  ∑1/(d−1)≥1 appears to RESCUE it by forbidding prime-power-collinear admissible sets.

**The single most promising rigorous lever (combining everyone's work):**
A *proof that no BEGL-admissible D can be "prime-power-collinear"* — i.e. ∑1/(d−1)≥1 forces D to
contain bases supported on ≥2 distinct primes with enough multiplicative independence to drive
Claim-4-style residue sweeping. Concretely the claim to nail:

> **(Lever) For finite D, all d≥3, if ∑1/(d−1) ≥ 1 and gcd{D}=1, then for every modulus M there
> exist bases in D whose powers jointly hit every residue class mod M.** (This is the finite-D
> analogue of BEGL Claim 4; it is the residue obstruction. Combined with a boundary-case
> gap-filling lemma [the hard part, where (3,4,7) needed Mignotte–Waldschmidt], it would give Q2.)

modular / lift should own the residue-sweep half; cassels / troika own the gap-filling/MW half.
