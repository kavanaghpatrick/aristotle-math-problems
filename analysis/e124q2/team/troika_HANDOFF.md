# troika HANDOFF — E124 / BEGL96 (Jun 10 2026)

## (1) PROVED / VERIFIED results + file pointers
- **gcd=1 necessity** (mechanism + proof): if g=gcd(D)>1 then for k≥1 every atom ≡0 mod g, so all
  n≢0 mod g missed ⟹ FALSE. k=0 escapes (d^0=1). → `troika_gcd_necessity.md`.
- **Mult-indep-pair lemma** (RIGOROUS, 5429 families): every admissible D (gcd=1,|D|≥2) has a
  multiplicatively-independent pair. Mult-dependence is an equivalence (classes=powers of common base);
  no indep pair ⟹ all powers of one c ⟹ c|gcd(D), contra. ⟹ MW always applicable for any admissible D.
  → `troika_generalization_mechanism.md`.
- **BEGL96 = s=1 only** (from the actual PDF, via scholar): paper proves (3,4,7) largest-hole 581 for
  k=1 ONLY, via MW |3^p−4^q|. The all-k Lean lemma `ne_zero_three_four_seven {k≠0}` is an OVER-CLAIM
  (`research solved` tag unjustified). Paper's general Thm 1 needs positive upper density (false for
  finite D). → `troika_347_reverse_engineered.md`.
- **Paper erratum** (3 engines): BEGL's "similarly" values off by +1 — correct largest-miss
  (3,5,7,13)=112, (3,6,7,13,21)=17, (3,4,5)=79; only 581 exact.
- **CORRECTED thresholds (3,4,7)**: 581 / **3,982,888** / **166,025,260** for k=1,2,3 (my earlier
  785743 / 57.75M were truncation artifacts — breaker/cassels/maverick all confirm corrected values).
- **Band-boundary mechanism**: exceptionals sit in thin bands just below base powers; it's a
  GRANULARITY failure (total atom-sum > n, yet n unreachable), not density. Cassels interval lemma
  underestimates N₀ by 200×–29000× ⟹ boundary case is genuinely non-elementary.
  → `troika_cassels_insufficient.md`, `troika_band_closure_mechanism.md`, `troika_synthesis_difficulty_located.md`.
- **Consolidated:** `troika_SUMMARY.md`.

## (2) WORK IN FLIGHT — exactly where I stopped
- **theorem_347_allk.md §C is WRITTEN then PARTIALLY CORRECTED** (with lift). §C.1 (MW bound usable
  form, C≈1.22 verified) and §C.2 (B₃+B₄ gaps unbounded ∝ top power, verified N=3.2e7) STAND.
  **§C.3/§C.3a/§C.4's "triple-alignment, closed by MW, complete-modulo-one-constant" framing is
  WITHDRAWN** — lift caught the flaw, I verified it: B₃+B₄ gaps have POSITIVE measure (8–21%), not
  →0, so "hole ⟹ triple alignment" is false. CORRECTED mechanism (verified, in the file):
  density-overlap + EQUIDISTRIBUTION — n>581 has min 10 (growing: 10→40→63) base-7 representations,
  each shift covers ~77% of a gap, union of ~log₇(n) shifts closes it. The right tool is
  CIRCLE-METHOD / Weyl equidistribution of {l·log7} mod the (log3,log4) lattice, NOT MW. MW only
  dispatches finitely many worst near-coincidences. → troika_C3_correction_tool_assessment.md.
  **This is the genuine DEATH POINT**: the theorem reduces to a base-7 equidistribution estimate over
  the B₃+B₄ gap bands — the open analytic core. NOT complete-modulo-a-constant.
- **Renormalization lane** (team-lead redirect): NOT started. This was to be my next lane after §C.

## (3) PRECISE NEXT STEPS for a successor
1. **§C is NOT closeable by transcribing an MW constant** (that was the withdrawn claim). The real
   open core: prove a base-7 equidistribution / exponential-sum estimate — that the base-7 subset-sums
   equidistribute across the B₃+B₄ gap bands so no n>X₀ is missed by every shift. Look at Mauduit–Rivat
   / Maynard digit-distribution machinery (scholar tool #12), NOT MW Cor 10.1. (Original step kept
   251–287, Cor. 10.1, to give X₀ an explicit numeric value (must be ≥581; the k=1 finite check forces
   it). Then theorem_347_allk.md is a finished unpublished theorem (label MW as cited input).
2. **Sanity-check §C.3 bridge** if lift hasn't: the claim "a hole at n survives only if every translate
   n−c (c∈B₇) lands in a B₃+B₄ gap, requiring a triple power-alignment" — verify the translate-tiling
   step is airtight (I verified the triple-alignment sparsity computationally: 5 triples spread<0.5 to
   1e9, never shrinking).
3. **Renormalization route** (the new-math lane, team-lead's redirect): combine sumset's Theorem C
   (deconvolution ∑B_d = L_k + T_k, L_k finite) with the verified recursion T_k=C_k+T_{k+1} to ask
   whether a SEED interval at level k+1 propagates DOWN to level k (not just up). If seed-existence is
   renormalization-stable, the whole conjecture reduces to ONE seed per D, which the k=0 theorem may
   supply. Coordinate with maverick (owns recursion) + modular (size-control). This has the right SHAPE
   to be uniform in both k and D — what MW cannot give.

## (4) TRAPS to beware
- **Truncation trap** (I got burned twice): NEVER trust "largest gap ≈ cutoff" as converged.
  Exceptionals cluster in thin bands JUST BELOW high powers of the bases and recur far above naive
  windows. Recompute at 2N, 4N; only a count frozen with margin + empty bands above is convergence.
- **General-D MW is a DEAD END** (scholar's guardrail, scholar_MASTER_TOOLLIST.md §I): constants grow
  with base heights + a ∀D proof can't run ∞ per-D finite checks. Do NOT invest in generalizing MW to
  all D. Individual-set MW (the (3,4,7) theorem) is fine.
- **The boundary case is non-elementary**: do not try to close ∑=1 families with Cassels/partial-sum
  density — it underestimates N₀ by 1000×. The obstruction is granular (isolated points), not density.
- **Quantifier drift**: the target is `∑_{d∈D} sumsOfDistinctPowers d k` (pointwise sumset) = subset
  sums of atoms {d^j : d∈D, j≥k}, each atom used ≤ once. Don't conflate with free-multiplicity.
