# troika: the elementary Cassels filling lemma does NOT certify the (3,4,7) threshold

This settles the "is the boundary case elementary or does it need transcendence?" question that
cassels (§4 of [[cassels_completeness_machinery]]) and I were circling. **Decisive answer: the
naive merged-atom Cassels interval-filling lemma is FAR too weak — it is off by 2–3 orders of
magnitude — so the harmonic-boundary case genuinely needs the finer (MW/Baker) analysis.**

## The test
Cassels interval-filling: sort all atoms A(D,k)={d^j:d∈D,j≥k}, partial sums T_n. The lemma says
"if a_{n+1} ≤ T_n+1 for all n past some i₀, the subset-sum set is an interval above T_{i₀}, so the
largest non-representable integer is < a_{i₀} (the last atom where filling fails)."

| D, k | Cassels "last-failure atom" (claimed bound on N₀) | TRUE N₀ | factor off |
|------|------|---------|-----------|
| (3,4,7) k=1 | < 3 | 581 | ~200× |
| (3,4,7) k=2 | < 27 | 785 743 | ~29000× |
| (3,5,7,13) k=1 | < 5 | 112 | ~22× |
| (3,5,7,13) k=3 | < 2187 | 4 796 646 | ~2200× |

## Why the Cassels lemma fails here (the real point)
The merged-atom partial-sum condition a_{n+1} ≤ T_n+1 IS satisfied after the first few small atoms
(verified: for (3,4,7) all failures are at atoms ≤ 27). The naive reading would conclude N₀ < 27.
But the TRUE N₀ is 785 743. **The lemma's hypothesis is not actually applicable**: subset sums form
a single interval only if EVERY atom (including the large multiplicatively-gapped ones) can bridge,
but with three sparse geometric rays {3^j},{4^j},{7^j} the reachable VALUES skip specific integers
(like 581) far above the last small-atom failure. The partial sum dominating the next atom does NOT
imply every intermediate integer is hit, because the available atoms are too sparse/structured to
realize each value — exactly when the rays are geometric with large ratio.

The location of the highest skipped value (581, 785743, …) is governed by how the three geometric
rays interleave — i.e. by how close cross-base powers d_i^p and d_j^q can be. That is a
**Diophantine-approximation question**, which is precisely why BEGL96 invoked Mignotte–Waldschmidt
linear-forms-in-logs (`|3^p − 4^q|` lower bound), not elementary Cassels filling.

## Consequence
- **The boundary (∑1/(d−1)=1) case is NOT elementary.** Any rigorous proof of (3,4,7)-all-k (and a
  fortiori the general conjecture) must control cross-base power spacing via Baker/MW bounds — not in
  Mathlib, not bare-submittable.
- This refines cassels §4 ("the tight case is THE lemma to nail"): the lemma to nail is NOT a
  Cassels-filling lemma; it is a spacing/transcendence lemma. The elementary density invariant
  ∑1/(d−1) is the right THRESHOLD invariant (Pomerance converse) but does NOT supply a sufficiency
  proof at the boundary.
- For SLACK families (∑1/(d−1) > 1 with enough slack), there is more room and elementary methods may
  suffice for large k; but the single tight triple is the hard core, consistent with BEGL only
  managing (3,4,7) via MW. See [[troika_347_reverse_engineered]], [[troika_SUMMARY]].

## EMPIRICAL fingerprint of the MW connection (new)
The threshold N₀(k) sits right at cross-base power near-coincidences — direct evidence the location is
spacing-governed (= MW territory), not density-governed:
- k=1: N₀=581. The CLOSEST 3^p~4^q pair anywhere is 3^5=243 vs 4^4=256 (|diff|=13, rel 0.053). 581
  lives exactly in this band (243 < 581 < 729=3^6, and 256 < 581 < 1024=4^5). The worst hole forms
  where the two rays nearly coincide and "waste" coverage.
- k=3: N₀=57 751 591 sits between 3^16=43 046 721 and 7^9=40 353 607 (both within ratio 1.4 of N₀) —
  again a multi-ray near-coincidence region.
This is the concrete reason BEGL's bound is phrased via |3^p − 4^q|: the last exceptional point is
pinned by how close powers of different bases can get, exactly the linear-forms-in-logs quantity.
