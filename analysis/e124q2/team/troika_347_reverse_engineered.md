# troika: (3,4,7) reverse-engineered — what BEGL96 ACTUALLY proves, and the all-k gap

Builds on scholar's paper dissection ([[scholar_BEGL96_proof_dissected]]) and sumset's scaling
([[sumset_reduction_scaling]]). I verified every claim below computationally.

## HEADLINE (answers the entry-point question scholar flagged to me)
**BEGL96 proves the (3,4,7) result ONLY for s=1 (k=1), not for all k.** The paper (§3, verbatim
lines 227–238 of _raw_begl96_fulltext.txt) states only: "the largest integer not in
Σ(Pow({3,4,7};1)) is 581," proved via the Mignotte–Waldschmidt bound `|3^p−4^q| > exp{ln3(p −
500 ln4 (8+ln p)²)}` (MW Cor. 10.1, linear forms in two logs) plus a finite check up to 581.

**Our Lean file `erdos124.ne_zero_three_four_seven {k : ℕ} (hk : k ≠ 0)` asserts (3,4,7) for ALL
k≠0.** That is STRONGER than what BEGL96 displays. The paper's general Conjecture covers all s, but
the only *proved* small-set instance shown is s=1. So the `category research solved` tag on the
Lean lemma for all-k is, at best, citing an extrapolation BEGL did not write down. This is a
provenance gap the team should flag (it does not affect the truth — see below — but affects what
counts as "known").

## Validation of my engine against the paper (and a paper erratum I found)
Computed "largest missing integer" at k=1 (two independent engines: numpy bitset + recursive
subset-sum, agree bit-for-bit):
| family | paper value | computed (CORRECT) |
|--------|-------------|--------------------|
| (3,4,7) | 581 | **581 ✓ exact** |
| (3,5,7,13) | 111 | **112** (paper off by 1) |
| (3,6,7,13,21) | 16 | **17** (paper off by 1) |
| (3,4,5) | 78 | **79** (paper off by 1) |
The three "similarly…" examples are each off by +1 in the paper; n=111, 16, 78 are all
REPRESENTABLE (verified by independent brute force). Only the MW-computed (3,4,7)=581 is exact.
Minor erratum, but worth recording since our formalization may cite these numbers.

## Anatomy of the last hole 581 (why MW is needed, not just Cassels)
- Atoms ≤581: base3 {3,9,27,81,243}, base4 {4,16,64,256}, base7 {7,49,343}.
- 581 is NOT expressible as (subset-sum of base3 atoms)+(base4)+(base7); 580 and 582–585 all ARE.
- The naive 1-D Cassels criterion (sort all atoms, check aₙ₊₁ ≤ 1+∑_{i≤n}aᵢ) FAILS only once
  (at atom 3) and is satisfied forever after — yet the true threshold is 581, far higher. So
  **the simple partial-sum/Cassels test does NOT explain 581.** The obstruction is granular: even
  when partial sums dominate, the *specific reachable values* leave holes, and the highest hole
  (581) is controlled by how close consecutive cross-base powers (3^p vs 4^q) can be. That gap
  control is exactly what MW linear-forms-in-logs provides. This is the genuine reason the
  harmonic-boundary single-triple case needs transcendence theory, not elementary density.

## Is the all-k claim TRUE? (computational evidence: YES)
Even though BEGL96 only displays s=1, the all-k statement appears TRUE. Converged thresholds
(full coverage verified above each, via R_k = 3^k S3 + 4^k S4 + 7^k S7):
  N₀(1)=581, N₀(2)=785 743, N₀(3)=57 751 591. Growth ≈ C·84^k (84=3·4·7), C≈100 — GEOMETRIC,
  not a tower. (k=3: zero gaps in [58.5M,117M], computed to N=130M.) See [[troika_scaling]].

## The route to a real all-k proof (for lift/cassels/the formalizer)
The MW method generalizes: for s=k, the relevant transcendence input is a lower bound on
`|3^p − 4^q|` (and `|3^p − 7^r|`, `|4^q − 7^r|`) with exponents ≥ k. MW Cor. 10.1 gives such bounds
uniformly. The completeness engine (scholar's Claim 1, the Cassels-type gap bound `≤ 2·b_N^{s+1}`)
then needs the per-base density ∑ b_i^{-(s)} — but at the harmonic BOUNDARY ∑1/(d−1)=1 this density
input is exactly critical, which is why BEGL's Claim 1 (needing β>2) does NOT apply and the MW
gap-control substitutes for it. **A formal all-k proof of (3,4,7) reduces to: (1) MW/Baker lower
bounds on |dᵢ^p − dⱼ^q| (NOT in Mathlib — this is the hard import), plus (2) a finite verification
that grows like 84^k.** Neither is bare-submittable; this is why E124-open(D, general k) is hard.

## Bottom line for the conjecture (general admissible D)
- gcd=1 necessity: settled ([[troika_gcd_necessity]], [[lift_gcd_necessity]]).
- Residue covering with gcd=1: settled ([[sumset_crt_residue_theorem]], [[modular_local_coverage]]).
- The REMAINING open core is the *archimedean/gap* half at the harmonic boundary: showing the
  exceptional set is finite. For (3,4,7) all-k this rests on MW linear forms. For general boundary
  D it is exactly the BEGL96 conjecture they call themselves "fairly far from" proving. No
  elementary closure exists; bare submission to a formalizer cannot supply the transcendence input.
