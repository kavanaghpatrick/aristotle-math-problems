# Prior-art sweep: the three candidate new-mathematics routes for Q2's (A)-half

**Author:** scholar. **Scope:** does prior art exist for any of the three directions the team is
considering to close the archimedean/gap-filling half (A) of E124 Q2 (cofiniteness of
`R(D,k) = ∑_{d∈D} d^k·B_d` at the harmonic boundary)? **Method:** live web search (Grok) across
MathSciNet/arXiv/Scholar + direct PDF/abstract checks + my own computations. **Confidence tags as
before: [PDF]/[SEC]/[COMP].**

> **BOTTOM LINE (all three routes):** Each route has strong machinery in a NEIGHBOURING regime
> (real Cantor sets / single fixed base / S-unit gaps), but in EVERY case there is a genuine,
> currently-unbridged gap to the discrete, MULTI-BASE setting Q2 requires. None is a known
> failure to avoid; none is a ready-made tool. The recurring obstruction is identical to the one
> the literature picture already exposed: **incommensurable bases (3,4,7) share no common
> arithmetic/Fourier/self-similar structure**, so single-base or single-attractor theory does not
> compose. This is precisely why Q2 is hard and why a real proof needs new mathematics. Below,
> the strongest available theorem per route and the exact gap to the seed.

---

## Route (a): self-similar / renormalization / IFS / automatic-sequence methods

**What exists (all REAL / measure-theoretic, [SEC]):**
- **Newhouse thickness** (1970s): if Cantor sets `C₁,C₂ ⊂ ℝ` have `τ(C₁)·τ(C₂) ≥ 1` then
  `C₁+C₂` contains an interval. Real compact sets only.
- **Astels 2000** [Trans. AMS, "Cantor sets and numbers with restricted partial quotients"]:
  sums of Cantor sets defined by digit/partial-quotient restrictions contain intervals; an
  explicit thickness-type criterion. Purely real.
- **Hochman–Shmerkin (2012–16)**: dimension/convolution results for self-similar measures and
  their sums on ℝ. Measure-theoretic; says nothing about discrete cofiniteness.
- **Automatic sequences:** `B_d` IS the support of a d-automatic indicator [SEC: Allouche–Shallit,
  *Automatic Sequences* 2003, §5.3–5.4]. But the additive-basis literature on automatic sets uses
  automata/kernel/Cobham arguments, NOT IFS renormalization. **No theorem says a finite sum of
  automatic 0/1-digit sets is cofinite.**

**The exact gap to the seed:** `B_d` is genuinely an IFS attractor:
`B_d = {0} ∪ (d·B_d) ∪ (1 + d·B_d)` [COMP, verifiable]. So an Astels/Newhouse "thickness ≥ 1 ⇒
sumset contains an interval" theorem is the PERFECT structural analogue — and `∑1/(d−1)≥1` smells
exactly like a discrete thickness condition. **BUT no discrete (integer-lattice) analogue of
thickness/Astels is proved anywhere.** Bridging real→integer is itself the novel theorem. This is
the SINGLE most structurally promising route (the analogy is tight) and simultaneously the one
with zero discrete prior art — i.e. genuinely new mathematics, not a reinvention.
> ACTION: worth troika/maverick formulating a discrete-thickness conjecture for `∑ d^k·B_d` and
> testing whether `∑1/(d−1)≥1` is the right thickness threshold. (Caution: real thickness uses
> the gap structure of a Cantor set; the integer analogue must handle the lattice and the d^k
> scaling. The k-dependence — N₀ ≍ d_max^k — is exactly a "thickness shrinks with k" phenomenon.)

## Route (b): circle method / exponential sums over digit-restricted sets

**What exists (all SINGLE-BASE, [SEC] + Maynard abstract [PDF]):**
- **Maynard 2019** [Invent. Math. 217, "Primes with restricted digits"; arXiv:1604.01041,
  abstract PDF-checked]: Hardy–Littlewood circle method on the indicator of base-10 restricted-
  digit integers; Fourier bounds via large sieve + geometry of numbers + Markov-process moment
  comparison; Harman's sieve on minor arcs. ⚠ **base 10 only; it is a BINARY problem (primes ∩
  missing-digit set); does NOT address additive bases / sums of restricted-digit sets.** The
  precise exponential-sum exponent is in the full 70-pp paper, not the abstract — Grok's quoted
  form `≪ X(log X)^{−c}` on minor arcs is [SEC], NOT verified; do not cite the exponent.
- **Mauduit–Rivat 2010** [Annals 171, sum-of-digits of primes] + **Dartyge–Mauduit 2000**
  [J. Number Theory 81, almost-primes with missing digits]: nontrivial bounds on `∑ e(α s_q(n))`
  and missing-digit indicators, SINGLE fixed base q.
- **Ellipsephic additive bases** [SEC: Banks–Shparlinski; Dartyge–Mauduit–Sárközy; Col]: results
  that `B_b + … + B_b` (enough summands, SAME base b) is cofinite / small exceptional set.
  **All intra-base.**

**The exact gap to the seed (a genuine structural obstruction, not just a missing paper):**
the three summands `d_i^k·B_{d_i}` live in INCOMMENSURABLE bases (3,4,7). Major-arc/minor-arc
analysis needs a common q-adic structure to approximate the product of generating functions; with
no common base, the major arcs of one set are minor arcs of another and the method does not
compose. **No circle-method result handles summands across different bases.** [COMP confirms the
sets share no Fourier structure.] So the circle method would need a genuinely new multi-base
decorrelation argument — plausible (Maynard's "decorrelating Diophantine vs digital conditions" is
the right spirit) but unwritten. Strongest realistic partial: a single-base ellipsephic basis
result might handle a SUB-problem (one base's contribution), but not the coupled multi-base sum.

## Route (c): multiplicative spread / S-unit distribution / gaps between powers

**What exists ([SEC]):**
- **Tijdeman 1973/76** [Compositio Math.]: consecutive S-units `u<v` (primes in fixed set S)
  satisfy `v − u ≫_S u/(log u)^C`, `C = C(|S|)` explicit (constant ineffective, via Baker). The
  merged atom set `{d^j : d∈D, j≥k} ⊂ ⟨primes dividing D⟩` is an S-unit set, so this applies.
- **Stewart / Stewart–Tijdeman 1986** + refinements: effective bounds on `|x−y|` for S-units;
  for `{3,4,7}` the best gap bound is still Tijdeman-type. Stewart's `|a^p − b^q|` bounds (same
  family as the Mignotte–Waldschmidt bound BEGL used) control the CLOSEST pairs only.
- **Pillai–Baker S-unit equations**: `a^x − b^y = c` has finitely many, effectively-bounded
  solutions ⇒ finitely many near-collisions among atoms.

**The exact gap — and a KEY INSIGHT that REVERSES the route's apparent value [COMP]:**
Tijdeman's bound shows S-units are SPARSE: gaps grow `≈ u` (I computed: for S=primes{2,3,7} the
max gap above 10⁶ is ≈2% of u and growing). **So the bare atoms `{d^j}` are FAR from complete by
themselves — completeness MUST come from the subset-sum closure (the full `B_d` structure), not
the atom spacing.** S-unit gap theory therefore controls the wrong object (atoms, not subset-sums)
and CANNOT directly give completeness. **No theorem gives a lower bound on the density/gaps of
SUBSET-SUMS of an S-unit set from multiplicative independence + `∑1/(d−1)≥1`.** The "multiplicative
spread" lever (my prime-power-collinearity bound) is real for ruling out the residue obstruction
(see `scholar_prime_power_collinearity_bound.md`), but S-unit gap theory does NOT extend it to the
archimedean half. Route (c) is the WEAKEST of the three for (A): it informs the residue side
(already team-proven) but the atom-sparsity result actively argues that atom-level methods fail.

---

## Synthesis & recommendation to the proof team

| Route | Strongest prior art | Regime | Gap to seed | Verdict for (A) |
|---|---|---|---|---|
| (a) IFS/self-similar | Astels 2000, Newhouse thickness | real ℝ | no discrete analogue exists | **most promising** — tight analogy (`∑1/(d−1)≥1` ↔ thickness), but needs a new discrete-thickness theorem |
| (b) circle method | Maynard 2019, Mauduit–Rivat | single base | multi-base decorrelation unwritten | promising but hardest; the incommensurable-base obstruction is real |
| (c) S-unit spread | Tijdeman, Stewart | atoms, not subset-sums | controls wrong object | weakest for (A); atoms are sparse, completeness needs subset-sums |

**Recommendation:** Route (a) (discrete thickness / self-similar) is the best bet — the IFS
structure of `B_d` and the thickness-flavoured `∑1/(d−1)≥1` condition line up almost perfectly,
and the k-dependence (N₀ ≍ d_max^k) reads naturally as "thickness degrades with k." Maverick's
`T_k = C_k + T_{k+1}` renormalization frame is exactly a discrete-self-similar approach and has NO
prior art to collide with — genuinely open territory. Route (b) is the fallback if a multi-base
exponential-sum decorrelation can be engineered (Maynard's spirit), but the incommensurable-base
obstruction is a hard, real barrier. Route (c) should be DEMOTED for the (A) half: its theorems
are about atom gaps, which are provably sparse, so it cannot supply completeness; reserve it only
for sanity-bounding near-collisions. **No route is a known dead end and none reinvents an existing
theorem — all three require genuinely new mathematics, consistent with Q2 being a real open problem.**
