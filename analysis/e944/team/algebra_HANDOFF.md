# algebra — HANDOFF (E944, snapshot 2026-06-10)

## 1. RESULTS (proven / verified — all χ cross-checked backtracking vs SAT via checkers.py)

**Verdict file:** `algebra_substrate_verdict.md` (full detail). Tools: `algebra_substrate.py`
(circulant/Schrijver/Kneser/products), `algebra_cayley.py` (non-cyclic Cayley scan).

- **State of the art (confirmed Jun 2026):** Skottova–Steiner 2025 (arXiv:2508.08703) closed ALL
  k≥5, ALL r≥1. **k=4 is the SOLE open case.** PDF text: `/tmp/ss2025.txt`. Martinsson–Steiner
  arXiv:2310.12891 text: `/tmp/ms2025.txt`.

- **The substrate of all modern constructions is a CIRCULANT / cyclic-group Cayley graph**
  (Jensen, Skottova–Steiner) or a Z_{k−1} structure needing a factorization (Lattanzio).

- **THE MECHANISM (central finding, rigorously verified):** In any vertex-transitive graph the
  automorphism group acts transitively on each edge-orbit; automorphisms preserve χ ⟹ **an edge
  is critical ⟺ its WHOLE orbit is critical**. So "no critical edge" requires EVERY edge-orbit
  redundant simultaneously. Verified orbit-uniform criticality in 100% of cases. For circulants
  "delete distance-class d" = passing to Cay(Z_N, D∖{d}), so the condition is "every
  single-distance removal keeps χ=4."

- **Computational verdicts (zero witnesses everywhere):**
  - Circulants Z_11..Z_19, |D|≤4: 1107 tested, **0 witnesses.**
  - 130 vertex-critical χ=4 circulants (Z_11..Z_23, |D| 2..4): in EVERY one, ≥1 distance class is
    critical → **0 symmetric witnesses.** (Extended Z_11..Z_25 |D|≤5 scan was running at snapshot,
    bg task `bc4mbgw94` — expected 0; not load-bearing.)
  - Non-cyclic Cayley (S3, Z2², Z2³, Z6, Z3², D4, Q8, Z12, Z2×Z6, Z2²×Z3, D6): **0 witnesses.**
  - Schrijver SG(6,2), SG(8,3): vertex-critical χ=4 but HAVE a critical edge. KG(6,2): not vertex-crit.

- **Why k−1=3 prime blocks Lattanzio:** composite k−1=a·b ⟹ Z_{k−1}≅Z_a×Z_b has TWO independent
  color-shift directions ⟹ obstructions witnessed redundantly ⟹ R realizable. Prime k−1=3 ⟹ Z_3
  simple, ONE direction ⟹ some edge-orbit forced critical. **R fails ⟺ k−1 prime, IN the
  vertex-transitive category.** Confirmed: product substrates (lex product) need k−1=a·b≥... so
  literally unavailable at k=4.

- **Hard constraints on ANY (4,1)-graph (SS Prop 5.1, proven):** min degree ≥6, edge-conn ≥6,
  |V|≥11, max degree ≤|V|−5, sparsest is **6-REGULAR**. SS open Problem 5.2 = "does a 6-regular
  (4,1)-graph exist?"

## 2. IN FLIGHT / incomplete

- **Lattanzio EXACT requirement:** paper (Discrete Math 258, 2002, 323–330) NOT freely retrievable;
  the "two-direction / factorization" mechanism above is RECONSTRUCTED from the k−1-composite
  condition + literature framing, not read verbatim. Confidence high but unverified against source.
- **Non-cyclic substrates ≥ order 12:** count took over the order≥12 non-abelian Cayley search
  (A4, D6, Dic3/Q12, D7…). My scan covered ≤ order 12. No overlap — coordinate with count.
- **ASSAULT direction (team-lead, post-snapshot): quasigroup / Latin-square / Steiner-system /
  voltage-graph substrates** — ASYMMETRIC (generically trivial automorphism group), the natural
  generalization of Lattanzio WITHOUT the primality death. NOT started (snapshot/idle order).

## 3. NEXT STEPS for successor (priority order)

1. **Quasigroup/Latin-square graphs** — the orbit obstruction (§1) ONLY kills symmetric substrates.
   Asymmetric Latin-square / STS / voltage constructions evade it. Build candidates, verify via
   `checkers.py`, score by critical-edge count, do per-failure analysis. This is THE lever.
2. **6-regular candidates on 11–14 vertices** (Prop 5.1 / SS Problem 5.2) — coordinate with
   hunter (search) / forge (surgery).
3. Retrieve Lattanzio 2002 PDF (try institutional access / Sci-Hub mirror / Jensen–Toft book §) to
   confirm the exact algebraic requirement verbatim.

## 4. TRAPS

- **VOCAB TRAP (gallai):** `IsCritical` = VERTEX-critical, NOT edge-critical. Kostochka–Yancey /
  Gallai density theorems are for EDGE-critical graphs and do NOT apply to the target. The target
  is precisely vertex-critical-but-NOT-edge-critical.
- **The orbit argument is NOT a closure.** It rules out symmetric substrates only; says nothing
  about asymmetric graphs. Do not let anyone report it as a negative resolution.
- **SS Lemma 2.1 (gluing) cannot bootstrap** the first (4,1)-graph — it only manipulates the ORDER
  of an existing witness. A genuine seed witness is still needed.
- DB `erdos_944` attempts are mirages; NEVER submit to Aristotle; compute for real.
