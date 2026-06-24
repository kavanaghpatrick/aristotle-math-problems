# E944 — Combinatorial Nullstellensatz / Alon–Tarsi attack (gallai, re-arm round)

TARGET: the irreducible core "every χ=4 vertex-critical graph has a critical edge" (f≤1), via the
GRAPH POLYNOMIAL P_G = ∏_{(u,v)∈E, u<v}(x_u − x_v) — a genuinely different object from the chromatic
polynomial (banned day-1 territory). k=5 reality check mandatory.

## The framework (verified correct)
- Alon–Tarsi / Combinatorial Nullstellensatz: G is 3-colorable ⟺ P_G has a monomial ∏ x_i^{d_i} with
  all d_i ≤ 2 and NONZERO coefficient. The coefficient = (#even orientations − #odd orientations) with
  outdegree sequence d (signed orientation count). Verified: K4 has 0 bounded-nonzero monomials
  (not 3-colorable ✓); each K4−e quotient has 12 (critical ✓); orientation-count = sympy coeff ✓.
- Criticality translation: e=(a,b) critical ⟺ P_G/(x_a−x_b) = P_{G−e} has a ≤2-bounded nonzero monomial.
- GENUINELY NEW vs B₁: the coefficients are SIGNED (mix of +1/−1, orientation parity), unlike the
  non-negative coloring count B₁. A parity/sign obstruction has no analog in the Potts/B₁ world.

## DEATH POINT — the homogeneity/degree wall (clean, rigorous, kills the lever)
The graph polynomial P_G is HOMOGENEOUS of degree m = |E(G)| (a product of m linear forms). So EVERY
monomial of P_G has degree EXACTLY m. A ≤2-bounded monomial (exponents in {0,1,2}) has degree ≤ 2n.
Therefore:
> **If m > 2n, P_G has ZERO ≤2-bounded monomials at all, so AT-3-colorability is FALSE by pure degree
> count — regardless of the true chromatic number.**

Verified: K_{2,2,3} (n=7, m=16 > 2n=14) is genuinely 3-CHROMATIC (3-colorable) yet has 0 ≤2-bounded
monomials, so is NOT AT-3-colorable. AT-3-colorability is STRICTLY stronger than 3-colorability, and the
gap is exactly DENSITY (m vs 2n).

### Why this kills the lever in the witness regime
A witness has m ≥ 3n (Theorem 3: δ≥6). So m ≥ 3n > 2n, meaning:
- P_G has no ≤2-bounded monomial → AT says "not AT-3-colorable" (vacuously consistent with χ=4, but
  carrying NO information — it would say this even if χ were 3).
- For every edge e, P_{G−e} has degree m−1 ≥ 3n−1 > 2n → also no ≤2-bounded monomial → AT says "e not
  critical" for EVERY edge, INDEPENDENT of true criticality.
So the Alon–Tarsi / CN criterion is BLINDED by density in exactly the regime that matters: it cannot
distinguish critical from non-critical edges in a dense witness, because the degree obstruction zeroes
out the entire ≤2-bounded monomial space. The signed-coefficient parity structure (the genuinely new
feature) never gets to act — there are no coefficients to be signed.

## VERDICT
The AT/CN graph-polynomial lever is DEAD, killed by the homogeneity/degree wall: AT-3-colorability
requires m ≤ 2n, but a witness has m ≥ 3n. This is the Alon–Tarsi analog of the chromatic-polynomial
DENSITY wall (Route 5 / saturation map) — same failure mode (the witness is too dense for the tool),
reached via a completely different object. The k=5 reality check is moot: the lever fails at k=4 before
k-specificity is even in play. (For k=4 colorings — q=4, ≤3-bounded — the witness m≥3n needs m≤3n, i.e.
the 6-REGULAR case m=3n is the ONLY one where the ≤3-bounded space is nonempty, and there the relevant
coefficient is the signed count of balanced Eulerian orientations (every outdegree=3); but this detects
χ(G)≤4 which is TRUE for a witness, not criticality — so it is also non-informative for the witness
question.)

## Honest residue
New toolkit, fast clean kill, precise reason: the graph polynomial's homogeneity makes Alon–Tarsi a
SPARSITY tool (needs m ≤ (q−1)n), and the witness is dense (m ≥ 3n) — so it joins density/potential/
zero-free on the "vacuous against a dense witness" side of the saturation map. The signed-orientation-
parity structure is genuinely new and un-banned, but the degree wall prevents it from ever engaging.
