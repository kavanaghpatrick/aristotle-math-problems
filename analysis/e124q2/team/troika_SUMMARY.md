# troika: E124 / BEGL96 — consolidated findings

All claims below verified computationally with ≥2 independent engines where load-bearing.
Cross-refs: [[scholar_BEGL96_proof_dissected]] (paper), [[sumset_reduction_scaling]] (scaling),
[[lift_sufficiency_mechanism]] (residue lift), [[modular_local_coverage]], [[breaker_density_terminates]].

## 1. Reformulation (settled, team consensus)
`sumsOfDistinctPowers(d,k) = d^k · B_d`, B_d = {0-1-digit base-d numbers}. So the open target is:
**is the atom multiset A(D,k) = {d^j : d∈D, j≥k} a COMPLETE SEQUENCE** (every large n a subset sum)?
i.e. is `R_k = ∑_{d∈D} d^k·B_d` cofinite, for admissible D (all d≥3, ∑1/(d−1)≥1, gcd(D)=1)?

## 2. gcd(D)=1 necessity — SETTLED (mechanism + proof)
If p|gcd(D), then for k≥1 every atom d^j (j≥1) is ≡0 mod p, so R_k ⊆ pℤ and all n≢0 mod p are
missed forever ⟹ conjecture FALSE. k=0 escapes because d^0=1∈B_d. Density-admissible gcd>1 families
exist for every g (so the hypothesis is non-vacuous). [[troika_gcd_necessity]], [[lift_gcd_necessity]].

## 3. What BEGL96 ACTUALLY proves — SETTLED (my reverse-engineering of the paper)
- The paper's only GENERAL theorem (Thm 1) assumes **positive upper density of the base set**
  (limsup A(n)/n > 0), which is FALSE for every finite D. **It does not cover our finite-set,
  harmonic-boundary conjecture.** BEGL say they are "fairly far from" proving the conjecture.
- The (3,4,7) small-set result is proved **only for s=1 (k=1)** — "largest integer not in
  Σ(Pow({3,4,7};1)) is 581" — via **Mignotte–Waldschmidt linear forms in logs** (bound on |3^p−4^q|),
  NOT by elementary density. **Our Lean lemma `ne_zero_three_four_seven {k≠0}` asserts the all-k
  version, which BEGL96 does not display** — a provenance gap on its `research solved` tag.
- **Paper erratum I found:** the "similarly…" values are each off by +1. Correct largest-missing:
  (3,5,7,13)=112 (not 111), (3,6,7,13,21)=17 (not 16), (3,4,5)=79 (not 78). Only (3,4,7)=581 exact.
  [[troika_347_reverse_engineered]].

## 4. Truth of the conjecture — STRONG computational evidence for TRUE
All harmonic-boundary gcd=1 families (the hardest case, ∑=1 exactly) have FINITE thresholds at
k=1,2,3 with the exceptional set terminating. **CORRECTED thresholds** — my earlier values were
truncation artifacts (breaker caught this); recomputed to N=70M (k=2) / N=300M (k=3), 3 engines:
  (3,4,7): N₀ = 581, **3 982 888**, **≥166 025 260** for k=1,2,3.
WARNING (load-bearing): exceptionals cluster in thin bands JUST BELOW high powers of the bases and
recur far above naive windows. NEVER trust "largest gap ≈ cutoff" as converged — recompute at 2N,4N.
(3,4,7) is the tightest small triple but NOT structurally special; the conjecture is robustly true.
The band structure is the BEGL96 mechanism fingerprint — see [[troika_generalization_mechanism]].

## 5. Where the genuine difficulty lives — the (A)/archimedean half at the boundary
The problem splits: (R) residue covering + (A) archimedean gap-filling.
- (R) is SETTLED: gcd=1 + the Residue Lemma (B_b surjects mod m when gcd(b,m)=1) gives full residue
  coverage mod every m. [[sumset_crt_residue_theorem]], [[lift_sufficiency_mechanism]].
- (A) is the OPEN CORE. **It is NOT an elementary density argument at the harmonic boundary.** I
  verified the 1-D Cassels partial-sum criterion (aₙ₊₁ ≤ 1+∑prev) does NOT explain the (3,4,7)
  threshold (it fails only once, at atom 3, yet N₀=581). The highest hole is governed by how close
  cross-base powers (3^p vs 4^q) can be — a transcendence question, which is exactly why BEGL needed
  MW/Baker linear-forms bounds. **A formal proof of even (3,4,7)-all-k requires importing Baker/MW
  lower bounds on |dᵢ^p − dⱼ^q| (not in Mathlib) + a finite check growing like (∏d)^k.**

## 6. Bottom line / strategic
- **Answer to the Lean `answer(sorry)`: almost certainly `True`** (all computational evidence + the
  BEGL96 conjecture itself predict True). But TRUE is the conjectured/hard direction.
- **No bare-submittable closure exists.** The open core needs transcendence theory (Baker/MW) that a
  formalizer cannot supply from a bare gap statement. This matches Tao's "lowest hanging fruit" being
  k=0 (Alexeev did that); the all-k / general-D boundary case is genuinely hard.
- **Softest real sub-target:** formalize the s=1 (3,4,7)=581 result by importing/axiomatizing the one
  MW inequality + a finite computation — this is what BEGL actually proved and is the only rigorously
  closed small instance. The general conjecture remains open and is not closable by current methods.
