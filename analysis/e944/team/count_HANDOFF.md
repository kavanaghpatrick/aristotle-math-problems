# count — HANDOFF (E944 extremal/counting ledger) — 2026-06-10

**Role:** extremal/quantitative ledger for Erdős #944, k=4 Dirac case (does a
4-vertex-critical graph with NO critical edge — a "(4,1)-graph" — exist?).
**Engine:** `critedge.py` (exact DSATUR χ, self-tested vs brute force, 0 disagreements);
later candidates routed through hunter's `checkers.py` (backtrack + SAT cross-check).

## 1. VERIFIED RESULTS (all reproducible; files in this dir)
- **Census n=4..7 COMPLETE** (`count_census_n4to7.md`, `enumerate.py`): ZERO witnesses;
  min #critical-edges = 6 (K₄); **n=5 has NO 4-vtx-critical graph**. 3rd independent
  enumeration agreeing with hunter (geng) + skeptic (geng+SAT) + forge (extended to
  n=8,9,10: min-critical-fraction 0.80, 0.47, 0.36 — no positive floor).
- **Best approximate witness: C₇(1,2)=complement(C₇)** (`count_approx_witness.md`):
  4-regular, 4-vtx-critical, HALF its edges non-critical. Mechanism: vertex-transitive ⇒
  criticality constant per edge-ORBIT; one full orbit (diff-2) non-critical. **Overall
  champion: C₁₃(1,2,5)** — 6-regular, n=13, satisfies ALL Prop 5.1 conditions, only the
  difference-1 Hamilton-cycle orbit critical (13 crit / 26 non-crit of 39 edges). skeptic
  independently verified this with dual χ-checkers.
- **r-hierarchy** (`count_r_hierarchy.md`): r=1 is the EASIEST case. k=4,r=1 TRUE closes
  Dirac (`variants.dirac_conjecture`) entirely (k≥5 done); FALSE kills all 3 theorems.
  The single Lean stmt that falls is `erdos_944.dirac_conjecture.k_eq_four`.
- **Impossibility-via-counting is DEAD** (`count_overlap_L3.md`, `count_density_ledger.md`):
  confirmed wall's verdict (global K-Y squeeze doesn't close) AND showed L3 overlap-counting
  fails — critical set = never-avoidable set = ⋂_H E(H) exactly, no surplus (all seven n=7
  graphs). Density window 3n ≤ m ≤ n(n−5)/2, n≥11; min-deg-6 floor TRIPLY confirmed.
- **Relaxations give no help** (`count_relaxation_probe.md`): integral=fractional criticality
  exactly, no LP gap.

## 2. SEARCHES RUN + WHERE THEY STOPPED (all COMPLETE, no live jobs)
- **Circulants** (`count_circulant_search.md`, `circulant_search.py`, `circulant_6reg_search.py`):
  610 6-regular 4-vtx-critical circulants, ALL 3-elt distance sets, n=11..40 → 0 witnesses.
  Degree-8 (|S|=4) added to n=24 → 0. Strengthens Steiner's circulant lean to arbitrary
  distance sets. **DONE — do not re-run.**
- **Abelian Cayley** (`count_cayley_search.md`, `cayley_search.py`): Z_a×Z_b 6/8-regular →
  double-bind (4-chromatic but lose vertex-criticality). **DONE.**
- **Non-abelian Cayley** (`count_nonabelian_cayley.md`, `count_nonabelian_cayley.py`):
  A₄,D₆,Dic₃,D₇,D₈,D₉,D₁₀,Dic₄,Dic₅,D₃×Z₃ order≤20 → 0 witnesses (only D₈ gave 48
  4-vtx-critical graphs, best 16 crit edges). **DONE.**
- No background jobs left running.

## 2b. ASSAULT MODE (annealing) — added 2026-06-10, see count_anneal_results.md
Recipe-A SA, scorer = exact #critical-edges + soft χ/vertex-crit penalties (SOFT
penalties unstuck forge's rigid manifold). SIX strategies; NO witness.
- Detection VALIDATED: scorer = 0 on jensen's real (5,1)-graph G_(5,2,2).
- FEASIBILITY CAVEAT: chains reaching <n/3 critE do it by dropping min-deg<6 (Prop
  5.1 forbids) — a mirage. On the feasible 6-regular manifold the floor is ≈ n.
- mod-3 DICHOTOMY (count_mod3_dichotomy.md): C_n(1,2,5) n≡1 = vtx-critical w/ critE=n;
  n≡2 = 0 critE but ALL verts non-critical. Family overshoots, never both.
- BASIN-HOPPING (count_basinhop.py): proximity's escape lever — 15 large-step hops
  from C₁₃(1,2,5) NEVER drop below 13 critE; the n/3 plateau is robust to local AND
  large-step moves. (Files: count_anneal*.py, estar_structure.py.)
- 3-way tension: dense ∧ vtx-critical ∧ no-crit-edge — any 2 reachable, never 3.
- Verdict: mild impossibility-lean for 6-regular case; heuristic, NOT a proof.

## 3. NEXT STEPS FOR SUCCESSOR
- **Symmetric route is empirically exhausted (orders ≤ 20).** Champion stuck at C₁₃(1,2,5),
  1/3 critical. Per archivist: Brown's k=5 witness is 17-vtx ASYMMETRIC, not Cayley. ⟹
  **pivot to ASYMMETRIC.** Take C₁₃(1,2,5), apply asymmetric surgery to kill the surviving
  difference-1 Hamilton-cycle orbit (add chords/gadgets around those 13 edges) WITHOUT
  breaking vertex-criticality — hand to forge / hunter's asymmetric 6-regular CEGAR.
- **Impossibility lever the counting side CANNOT touch** (from archivist + Jensen-Siggers):
  prove "|E*| ≥ 1 always" (E* = critical-edge subgraph never empty), possibly via "E* is
  connected/spanning of positive size." This is a FINE 3-coloring-structure claim (wall's L2
  potential / gallai's rigidity), NOT cardinality. My L3 result proves counting won't do it.

## 4. TRAPS (do not repeat)
- `IsCritical` = **VERTEX-critical**, not edge-critical (gallai's vocab trap). K-Y/Gallai
  density transfers via a minimal spanning edge-critical H⊆G; the Gallai-tree STRUCTURE does not.
- **No upper bound on e(G)** — vertex-critical graphs densify freely. Do NOT hunt a density
  ceiling (gallai + wall confirmed). Target the SPARSEST witness: 6-regular (Steiner Prob 5.2).
- **Circulants/symmetric**: provably/empirically near-miss but never 0 critical edges at k=4.
  Don't re-sweep them. The diff-1 (odd-girth/Hamilton) orbit is the stubborn survivor.
- Net calibration: **no counting/density/relaxation obstruction blocks a witness** ⟹ leans
  TRUE-but-hard-to-construct; witness (if any) is asymmetric, 6-regular-or-denser, n≥11.
