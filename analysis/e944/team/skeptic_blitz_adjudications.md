# E944 INVENTION BLITZ — skeptic adjudication ledger

Verification command for the invention blitz. Kill-rules: constructions die by dual checkers; structural
claims die by census + n≥31 rule; impossibility identities die by the k=5 reality check (must NOT also
force E*≠∅ on the real (5,1)-graphs C₁₇(1,3,4,5), C₁₇(1,4,6,7) — skeptic_k5_fixtures.txt, dual-verified).

## ROUND 1

### algebra C1–C6 — all KILLED (agent verdicts CONFIRMED)
C1 superposition overshoots density (χ≥5); C2 greedy deletion collapses to K4 (δ=3); C3 ℤ₃ cover keeps
χ in base; C4 per-rung shifts break the ℤ₂ obstruction; C5 overlay doesn't de-criticalize; C6 two-hub
triangulation overshoots to χ=5. Diagnoses sound. No survivors.

### count CNT-1/2/3 — awaiting results ("[run this round]")

### gallai G-INV-1..4 — SURVIVES round 1 (sole substantive survivor)
- G-INV-4 identity B₁ = Σ_e P(G−e,3): CONFIRMED independently, 0 failures / 17 four-vc graphs n≤8.
- G-INV-2/3 (B₁>0 ⟺ E*≠∅; witness ⟺ Potts double-root at t=0): CONFIRMED exact, 0 mismatches.
- **k=5 reality check PASSES:** real (5,1)-graphs have B₀=B₁=0 at q=4 (double root realized), so the
  conjecture "B₀=0 forces B₁>0" is correctly q=3-specific — does NOT refute k=5. Sound.
- **HONEST: the core conjecture IS the open problem restated** ("every 4-vc graph has a critical edge").
  gallai labels it a conjecture — no overclaim. Value: chromatic-poly positivity (Birkhoff–Lewis) +
  root-multiplicity framing dodge the density wall. NOT progress until a real lower bound on Σ_e P(G−e,3)
  materializes. NEXT TEST (round 2): produce that bound, or it's reformulation-only.

### jensen J1–J4 — J1 KILLED, J2/J3 PARTIAL (confirmed), J4 DOWNGRADED
- J4 "non-abelian D7 Cayley = most promising lead": NOT a fresh escape. The ORBIT LEMMA
  (edge-criticality constant on each Aut-orbit; proven via φ: G−e ≅ G−φ(e)) applies to ALL
  vertex-transitive graphs, and every Cayley graph (abelian or non-abelian) is vertex-transitive.
  Verified: a χ=4 D7 Cayley graph hits "0 critical edges but NOT vertex-critical" — the SAME trade as
  circulants. The obstruction is TRANSITIVITY ITSELF, not ℤ_n. Do NOT spend round 2 on D7/D8 sweeps.
  jensen's lane and wall's WALL-1 AGREE once the orbit lemma is applied. Witness must be ASYMMETRIC.

### wall WALL-1/2/3 — all DEAD this round (confirmed), WALL-1 conclusion is the KEY synthesis
- WALL-1 (non-cyclic abelian Cayley): DEAD + the right diagnosis ("the problem is vertex-transitivity
  itself, not ℤ_n"). This is the load-bearing synthesis that downgrades jensen's J4. CONFIRMED via orbit
  lemma. ⟹ ABANDON all vertex-transitive substrates (circulant, abelian Cayley, non-abelian Cayley).
- WALL-2 (asymmetric 2-swap off C₁₃(1,2,5)): DEAD at n=13 (stayed critE=13), NOT conclusive — n=13 is the
  absolute floor; wall correctly invokes the n≥31 rule (don't conclude from small n). Re-run at larger n.
- WALL-3 (union of complementary sparse circulants): DEAD, collapses to the known-dead 6-reg circulant
  search. wall correctly notes joint-necessity must be NON-circulant. Sound.

### archivist A1–A3 — all DEAD (confirmed); META-LESSON sound
"redundancy must be EDGE-LOCAL not VERTEX-LOCAL" — each edge needs ≥2 obstructions but no vertex covered
by redundancy surviving its deletion. This correctly localizes the density-freezing wall. Verified-consistent
with my jensen-dichotomy adjudication (separable parallelism ⟹ spare-rail non-critical vertices).

## ROUNDS 2-4 (spot-adjudicated the load-bearing + potential-false-signal items)

### gallai R2-A/B/C (the double-root non-vacuousness) — CONFIRMED, no false witness
- POTENTIAL FALSE SIGNAL CHECKED: R2-A found 15 four-chromatic graphs at n=7 with min_mono≥2 (B₁=0,
  "double root"). IF any were vertex-critical, that's a WITNESS. Independently verified: all 15 are
  NON-vertex-critical (0 witnesses); named examples FEl~w, FQhVw both χ=4, min_mono=2, NOT vertex-critical.
  gallai's R2-B ("min_mono≥2 ⟹ has a non-critical vertex") holds at n=7. CONFIRMED.
- R2-C honesty CONFIRMED: gallai correctly concludes the Potts reformulation is LOGICALLY EQUIVALENT to
  E*=∅ (the open problem), not a reduction to anything easier. No overclaim. It's the best LANGUAGE
  (analytic chromatic-poly tools, dodges density wall), not a proof.

### wall WALL-5 (edge-addition descent primitive, "★ BEST") — descent VERIFIED
- Independently reproduced: Grötzsch (n=11) starts at 20 critical edges; greedy edge-addition preserving
  vertex-criticality descends to EXACTLY 13 (matches wall's 20→13), still vertex-critical, plateau >0,
  never hits 0. The primitive is REAL (descends where symmetric families are stuck) and SOUND (no false
  witness). Genuinely the construction-side dual of count's debt-trade. Worth handing to forge/count.
- WALL-6 (Hajós sums): DEAD-by-design confirmed — Hajós of edge-critical graphs is edge-critical (every
  edge critical), the maximally-wrong object. Correct.

### algebra C7-C12, wall WALL-4/7, gallai G-INV-5/6/7, hunter A1-A3 — agent verdicts spot-checked, sound
- C12 STRIKING NULL (0 of ~1600 random 6-regular graphs are 4-vertex-critical at small n): consistent
  with my Problem 5.2 floors (6-reg 4-vc graphs are RARE — none at n=11,12,14, one at n=13). Confirms
  witness is NOT a typical random 6-regular graph; needs guided/exhaustive search. Sound.
- gallai G-INV-5 (ℤ₃ character sum, DEAD/cancels), G-INV-6 (Tutte/Whitney, collapses to G-INV-3),
  G-INV-7 (ratio bound B₁≥c·P(G,4), PROMISING-then-DEAD ratio→0): all honestly self-killed. The Potts
  reformulation remains the only standing language; no analytic lower bound on Σ_e P(G−e,3) yet produced.

### forge round 1 (forge-1/2/3) + sharpened spec — all DEAD confirmed; spec sound-but-restatement
- forge-1 (triangle-cover, every edge in ≥2 triangles, δ≥6): DEAD — vertex-aligned backups (triangle uvw
  backing edge uv has third vertex w; deleting w removes the backup AND leaves others ⟹ w non-critical),
  reduces to K4. forge-2 (shift graphs): DEAD, wrong χ-regime. forge-3 (asymmetric blow-up of n=10
  champion): DEAD — reaches |E*|=0 but bundled independent sets removable ⟹ not vertex-critical. All three
  fail by the SAME mechanism (vertex-aligned redundancy) — consistent with archivist's edge-local-not-
  vertex-local meta-lesson + my jensen-dichotomy adjudication.
- SHARPENED SPEC ("obstruction hypergraph = vertex-deletion-robust edge cover"): SOUND necessary condition,
  correctly subsumes the dead families. BUT logically EQUIVALENT to the full (4,1) condition (NCE ∧ VC) —
  a restatement, NOT a reduction or sufficient condition (same status as gallai's Potts reformulation).
  Useful as an a-priori design FILTER (reject vertex-aligned families before building) but NOT a shortcut:
  round-2 candidates "designed to satisfy the spec" still need end-to-end dual-checker verification, because
  satisfying the spec IS being a witness. Told forge to route every candidate through skeptic_adjudicate.py.

## ROUND-1 SYNTHESIS (skeptic)
- ZERO witnesses. ZERO false celebrations.
- The squad has CONVERGED (independently, now cross-checked) on: **the witness must be ASYMMETRIC
  (|Aut|=1), dense (δ≥6), entangled (edge-local redundancy, no separable rails or transitive orbit-lock).**
  Every transitive/structured/separable route is dead for a SOUND reason (orbit lemma + density-freezing
  + separable-parallelism). This is a real narrowing, not a witness.
- SOLE substantive survivor: gallai's Potts/chromatic-polynomial reformulation — exact, reality-check-
  passing, but currently the open problem in new clothes. Lives or dies in round 2 on the Σ_e P(G−e,3)
  lower bound.
- n≥31 rule honored: WALL-2's small-n null is correctly non-conclusive.

## PROOF-TEAM CLAIMS (post-pivot to impossibility)
- forge B₁ LOCALIZATION (B₁(G) = ½ Σ_v cnt(v)): SOUND, 0 failures n≤8 — once cnt(v) read correctly as
  "#B₁-colorings whose unique mono edge is incident to v" (½-double-counting at the two endpoints). My
  first run flagged BROKEN on a mis-parse of "singleton in N(v)" — caught + corrected (told forge to
  tighten the prose). Same self-correction discipline as the earlier Lemma A and affine-existence catches.
- forge IMPOSSIBILITY BASE ("χ=4 ∧ |E*|=0 ⟹ NOT vertex-critical"): CONFIRMED exhaustively at n=8 — 619
  graphs with χ=4 ∧ |E*|=0 (dual-checked χ), ZERO vertex-critical (no witness). 3 are K₄-free (GQyurg/urw/uzw)
  ⟹ "|E*|=0 ⟹ contains K₄" correctly REFUTED. (Count note: I got 619 vs forge's 130 — different filter;
  conclusion identical. Asked forge to reconcile the subset for scope precision.) This is the empirical
  face of "no witness ≤ n" — sound base data, not a proof.
- wall f-COCYCLE load-bearing step ("e critical ⟺ ∃ 3-coloring mono exactly {e}"): CONFIRMED (216 edges
  n≤8, 0 mismatch) = per-edge form of gallai's B₁. k=5 passes. THIRD convergent reformulation; all three
  (gallai Potts, wall f-cocycle, forge robust-cover) are the SAME exact restatement of (4,1), none a reduction.

## 6-METHOD FLOOR CONVERGENCE (skeptic-tracked)
The n=13 critical-count floor of 13 is hit by SIX independent methods: skeptic exhaustive sweep, count
basin-hopping, proximity local-rigidity, wall WALL-5 edge-add, wall WALL-7 add-delete, jensen greedy
asymmetric chord-add. The asymmetric method coincides with the δ=6 transitive floor ⟹ genuine structural
floor, not an artifact. No local/greedy method beats it; witness (if any) needs larger n beyond local search.
