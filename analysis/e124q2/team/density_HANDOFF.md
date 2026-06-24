# density HANDOFF — Erdős #124 (open BEGL96 part), density/mass side

## 1. VERIFIED RESULTS (all EXACT computation; cross-validated with breaker/sumset/modular/scholar)

- **Threshold ∑1/(d−1)≥1 is a MAX-REACH TILING condition, not cardinality.** Counterexample:
  (3,5) passes entropy bound (∑log2/logd=1.06≥1) yet ~40% incomplete to 10^8. Worst-case reach of
  B_d = exactly 1/(d−1), attained just below a power of d. → `density_threshold_ledger.md` §1–2.
- **Constructive proof of Pomerance's converse** (the proven Lean lemma) via Weyl equidistribution:
  ∑<1 ⟹ missing block just below d_min^m for ∞-many m. Concrete: (3,6,7), n=40,342,197 unreachable
  by exactly 1 (brute-force verified). → `density_pomerance_converse_constructive.md`.
- **Two-regime split (the open core located):** Regime A (∑<1) top-of-power gaps recur forever →
  incomplete; Regime B (∑=1, the hypothesis) combinatorial gaps VANISH, only transcendence spacing
  |3^p−4^q−7^r| (Mignotte–Waldschmidt) remains. → ledger §6.
- **Prediction formula (VALIDATED):** first top-of-d_min^m gap at smallest m with
  (d_min^m−1)/(d_min−1)+∑_{d>d_min}maxB(d,d_min^m−1) < d_min^m−1. Predicts (4,5,6)→241,025
  (matches sumset's scan + my fresh checker). (3,5,7)→3^60; (5,6,7,8)→5^31. → ledger §4b.
- **No admissible D is prime-power-collinear (settles scholar's test).** T_p=∑_{j≥1}1/(p^j−1) maxes
  at T_3=0.682<1; p=2 towers force gcd>1. ⟹ admissible D carries ≥1−T_p≥0.318 mass off any single
  prime tower = forced multiplicative spread, the structural antidote to Melfi's pathology.
  → `density_no_prime_collinear_lemma.md`.
- **Two mass quantities reconciled (with modular):** coarse max-reach mass (=∑1/(d−1),
  scale-invariant in k) vs fine term-density (∑d^{1−k}/(d−1), decays ~d_min^{−(k−1)}). Coincide at
  k=1, diverge for k≥2. Completeness carried by COARSE mass + transcendence; fine density is meant
  to collapse. → ledger §7.
- **k-scaling, tight family (3,4,7):** N0(k)=581(k=1, matches BEGL96), 3,982,888(k=2),
  166,025,260(k=3) — finite per k, super-exponential. Bit-for-bit match with breaker's engine.

## 2. WORK IN FLIGHT / where I stopped
Nothing half-done. All claims above are written up and messaged. Last action: integrated modular's
term-density as ledger §7. I was about to go idle when the snapshot order came.

## 3. NEXT STEPS for a successor
- The open problem is now pinned to ONE statement (Regime B): prove that for every admissible D
  (∑1/(d−1)≥1, gcd=1) the transcendence spacing never re-opens a nested top-of-power gap above
  n0(k), uniformly in D,k. This is BEGL96's (3,4,7)-via-Mignotte–Waldschmidt, generalized.
- Concrete sub-task: make the equidistribution converse proof fully rigorous (the o(1) uniformity
  in `density_pomerance_converse_constructive.md` proof sketch).
- Possible: quantify the NESTED gap recursion (deficit-in-(B_{d>d_min}) gap) — I characterized the
  simple top-of-power gap exactly but the nested one only qualitatively. A recursion bound here
  might give an effective n0(k) for general D (currently only transcendence gives it).

## 4. TRAPS (heed these)
- **Finite "density→1" is NOT cofiniteness.** Sub-threshold families (∑<1) look cofinite to 10^8+
  because their first gap sits near d_min^m for large m (e.g. (3,5,7)→3^60). The proven converse
  settles ∑<1 ⟹ not cofinite; trust it over any finite scan. (sumset + modular + I all hit this.)
- **breaker's k=3 value for (3,4,7) is 166,025,260, NOT 57,751,591** (57.75M was a false freeze;
  deeper straggler at 166M). Require TWO stable doublings with max<N/2 before trusting any "freeze."
- **Don't conflate the two mass quantities.** "Mass survives scaling" is true ONLY for the coarse
  max-reach mass; the fine term-density correctly collapses for k≥1.
- **Entropy/cardinality threshold (∑log2/logd) ≠ the real threshold (∑1/(d−1)).** They differ;
  (3,5) shows entropy is strictly too weak.

## Files
`density_threshold_ledger.md`, `density_pomerance_converse_constructive.md`,
`density_no_prime_collinear_lemma.md`, `code/{sumset.c, sumset_k.c, missing.c}` (all EXACT engines).
