# breaker HANDOFF (Erdős #124 open part, k≥1 BEGL96 conjecture)

## Role: disprove route + quantitative engine backbone. Verdict: conjecture robustly TRUE.

## (1) FINAL VERIFIED RESULTS + pointers
- **Exact engine**: `breaker_engine2.py` — `exceptional2(D,k,N)` → numpy array of non-representable n≤N.
  Cross-validated bit-for-bit vs engine1 (`breaker_engine1_ref.py`) AND density's independent C engine.
  Exactness proof: each a_d ≤ n ⇒ bounded DP with cutoff d^j≤N is exact for all n≤N.
- **Reduction** (shared, sumset): S(d,k)=d^k·B_d, so n repr ⟺ n=∑_d d^k·b_d, b_d 0/1-digit base d.
- **Strict-verified thresholds n₀(D,k)** (largest non-representable), file `breaker_FINAL.md`:
  (3,4,7): 581 / 3,982,888 / **166,025,260**  [k=1/2/3; independently confirmed by maverick, cassels,
   troika, density]. CORRECTED from earlier wrong values 785743 (k2) and 57,751,591 (k3) — both false
   freezes. All 6 knife-edge sum=1 families + 45 small families finite at k=1,2,3. NO counterexample.
- **MW shadow** (with scholar), `breaker_proofside.md` addendum + `breaker_band_collapse.py`:
  per-band exceptional count over [4^J,4^{J+1}) PEAKS then COLLAPSES to 0 (2069→204→6→2→0). This IS
  the finiteness, and it tracks the Mignotte–Waldschmidt gap min|4^J−3^p|. Backs BEGL96's transcendence
  mechanism.
- **Proof-side deliverables** `breaker_proofside.md`:
  (a) (★) pinned: layered offset sum C_1+…+C_L residue coverage is LOGARITHMIC — L_min(D,p^a) ~ c·a,
      coverage-lag slope c (=1 for (3,4,7), the hard extremal; 0.33–0.67 others). Engine
      `breaker_offset_layers.py`. (maverick refined: seed at L≈log_{d_max}n₀(k)+O(1).)
  (b) Prime-tower harmonic mass capped: single prime's full power-tower carries mass <1 (p=3: 0.682
      sup; realized max over 90069 admissible families 0.6635). ⇒ ∑1/(d−1)≥1 forbids Melfi single-tower
      degeneracy; every admissible D has ≥0.336 mass on multiplicatively-independent bases.
  (c) Scaling law conjecture: n₀(D,k)=d_max^{(1+o(1))k}; leading exponent set by d_max, not c.
      (cassels: the simple C·d_max^k law FAILS at the boundary β=1; per-step ratio non-monotone.)

## (2) IN FLIGHT
- **(3,4,11) anomaly** [team-lead's decisive task]: **RESOLVED — deep straggler trap, converse SAFE.**
  β=14/15=0.933<1; cassels saw it apparently COFINITE at k=1 (N₀=1595 to 300M). I tested the k=0 case
  (what the converse is actually about; valid chain: T_1⊆T_0 ⟹ k=1 cofinite ⟹ k=0 cofinite ⟹ β≥1):
  (3,4,11) k=0 has ZERO exceptions to **9×10⁹** (validated fast atom-sieve `breaker_atom_sieve.py`,
  ~50s/9e9). BUT the Pomerance converse is EXACT with no extra hypotheses (lit-confirmed): β<1 ⟹
  infinite uncovered set of arbitrarily-low density. So the first exception EXISTS beyond 9e9 — the
  deepest straggler yet. CONVERSE STANDS. Not unique to (3,4,11): (3,5,7),(3,4,10),(3,4,12) all β<1,
  zero misses to 200M. Onset scale is base-sensitive transcendence. → CLAIMS.md breaker section.

## (3) NEXT STEPS for successor
- Finish the (3,4,11) scan past 11^9≈2.36B (and ideally 11^10). The trap predicts a missing block just
  below a high power of 11, beyond cassels' 300M window. If found → converse safe, anomaly dissolves.
  If genuinely cofinite to ~10^10 → escalate (either converse mis-stated or k=1 case is exotic).
- Proof side is where the win is: lift k=0/Alexeev to k≥1 (gcd=1 gives local per modular's lemma (L);
  density/MW gives size). The open core is the uniform-in-k coverage-lag bound (transcendence).

## (4) METHODOLOGY RULES (a successor MUST follow)
- **Strict 2-doubling freeze**: never declare a "true max" / "terminated" until the exceptional COUNT
  is unchanged across TWO consecutive N-doublings AND max-exc < N/2 BOTH times. A single plateau LIES
  (785743, 57.75M both broke). The trap bites when some d_max^j sits just above your search bound.
- **Density, not max-exc**: judge finiteness by whether the COUNT grows linearly in N (positive density
  = infinite/FALSE) vs plateaus (finite). Check UPPER-HALF complement density (maverick), not just
  largest-miss — a sparse persistent-gap complement is the dangerous false-positive shape.
- **Ignore box-counting** ∑log2/logd>1 (maverick: over-predicts; {3,4},{3,4,9} satisfy it but are NOT
  cofinite). The real boundary is harmonic ∑1/(d−1)≥1.
- A "counterexample" needs positive-density-in-N misses + a proof the exceptional set is INFINITE.
  Large n with no bounded-search representation is EVIDENCE, never proof. NEVER submit to Aristotle.
