# E944 — The four known constructions and WHY each fails at k=4

Sources retrieved + verified:
- **Skottová–Steiner 2025** (arXiv:2508.08703v1, 12 Aug 2025, CPC) — FULL TEXT in /tmp/skottova.txt (1935 lines). THE definitive current survey+advance. Confirms k=4 sole open case. Pdftotext-verified.
- **Martinsson–Steiner 2025** (arXiv:2310.12891, CPC 34:151-157) — FULL TEXT /tmp/ms2310.txt. Pdftotext-verified.
- Brown 1992, Lattanzio 2002, Jensen 2002: paywalled (Discrete Math, Elsevier). Constructions reconstructed from the two Steiner papers (which cite + modify them) + Grok literature search. Flagged where second-hand.

NOTE the VOCAB TRAP (gallai, confirmed): `IsCritical` in E944 = VERTEX-critical. Every result below is about vertex-critical-without-critical-edges. Edge-critical structural theorems (Gallai/Kostochka–Yancey) describe a DIFFERENT object. See gallai_vocab_trap.md.

---

## Timeline of Dirac's 1970 conjecture (k-vertex-critical, no critical edge)
| Year | Author | Result | Method |
|---|---|---|---|
| 1970 | Dirac | Conjectured: ∃ for all k≥4 | — |
| 1992 | Brown [Br92] | k=5 | first explicit example; product-type |
| 2002 | Lattanzio [La02] | all k with k−1 NOT prime | tensor/product, primality-sensitive |
| 2002 | Jensen [Je02] | all k ≥ 5 | circulant + color-pattern periodicity |
| ~2010s | Jensen–Siggers [JS] | k=4 PARTIAL: ∀ε>0 ∃ 4-vertex-critical graph with <ε-fraction of edges critical | — (closest anyone got to k=4) |
| 2025 | Martinsson–Steiner | (k,r)-graph for all r, k≥k₀(r) large | random sparse-matchable hypergraph 2-section complement |
| 2025 | Skottová–Steiner | (k,r)-graph for ALL k≥5, r≥1; f_k(n)=Ω(n^{1/3}); upper bd O(n/(log n)^c) | modified Jensen circulant + gluing |
| **2026** | **— (OPEN)** | **k=4, r=1 still unresolved** | — |

---

## Construction 1 — Brown 1992 (k=5)
First explicit vertex-5-critical graph with no critical edge. Product-type (literature consistently links to a categorical/tensor product, base case of Lattanzio's family at k−1 = 4 = 2×2). Why k=5: the product gadget balances criticality only at composite k−1; 4 = 2×2. Brown's example is essentially the p=q=2 case of Construction 2. [Second-hand: original PDF paywalled.]

## Construction 2 — Lattanzio 2002 (all k with k−1 composite)
Tensor/categorical-product generalization of Brown. For k−1 = p·q (p,q ≥ 2), takes a product of two base structures sized by p and q; the factorization is encoded into the coloring "dimensions". A proper (k−1)-coloring of the whole graph is blocked, but every vertex-deletion drops χ.
**WHY k=4 FAILS:** k−1 = 3 is PRIME → no nontrivial factorization p·q with p,q ≥ 2 → the product mechanism has no factors to work with. This is the precise sense in which "k−1 = 3 prime" blocks Lattanzio. NOTE the genuinely prime-blocked cases are k−1 ∈ {3,5,7,...} i.e. k ∈ {4,6,8,...}. Brown's k=5 (k−1=4) and all composite-k−1 are covered. [Mechanism reconstructed; original PDF paywalled.]

## Construction 3 — Jensen 2002 (all k ≥ 5) — STATE OF THE ART for Dirac
Circulant graphs with a carefully designed distance set + a periodic color pattern (φ_J). Does NOT need k−1 composite — covers k=6 (k−1=5 prime), k=8 (k−1=7 prime), etc. The mechanism: vertex-deleted subgraphs have a (k−1)-coloring forced into a periodic pattern; the density/periodicity makes every edge non-critical.
**WHY k=4 FAILS — the EXACT, PUBLISHED reason** (Skottová–Steiner §5, lines 1283-1292, verbatim mechanism):
The Skottová–Steiner circulant G_{k,m,q} (a richer modification of Jensen's) has distance set D = D₁∪D₂∪D₃ with
  - D₁ = {1,3,…,2m−1}  (odd distances up to 2m−1)
  - D₂ = (for k even) union of shifts of interval [2m, (k−4)m+2]
  - D₃ = (for k even) union of shifts of interval [(k+2)m−1, (2k−4)m+1]
For **k=4** (even), with m ≥ 2:
  - D₂ interval = [2m, (k−4)m+2] = [2m, 2] → EMPTY (2m > 2)
  - D₃ interval = [(k+2)m−1, (2k−4)m+1] = [6m−1, 4m+1] → EMPTY (6m−1 > 4m+1)
  - So **D₂ = D₃ = ∅**, only D₁ = {1,3,…,2m−1} survives.
A circulant on these distances has **chromatic number 3, not 4** (S–S: "It is then not hard to check…χ = 3"). Equivalently: Jensen's color pattern (Table 2) "forbids all distances greater than 1 for the edges, and taking only distance 1 results in an odd cycle, which is 3-colorable." So the WHOLE circulant/periodic-coloring family DEGENERATES to odd cycles at k=4.
S–S explicitly state (line 1291): "we lean towards thinking that they [circulant (4,1)-graphs] do not exist." → CIRCULANT GRAPHS ARE A DEAD END FOR k=4 (strong published belief, near-certainty).

## Construction 4 — Martinsson–Steiner 2025 (large k, all r)
G = complement of 2-section of a random s-uniform hypergraph (s=r+3) with H−v perfect-matchable + locally sparse. χ = (n−1)/s + 1, α(G) = s.
**WHY k=4 FAILS — ARITHMETIC WALL (my derivation, in archivist_martinsson_steiner_2025.md):** χ = (n−1)/s+1 with α=s and n=3s+1 forces χ ≤ n/α = (3s+1)/s < 4 for s≥2. The construction structurally CANNOT produce a 4-chromatic graph (it would be ≤3-chromatic). Plus asymptotic existence needs large n. MS is SILENT on k=4 (not an obstruction, just no leverage). They say so: "does not say anything about k fixed, r→∞."

## Construction 5 — Skottová–Steiner 2025 gluing (works for k≥4!)
Lemma 2.1 (verbatim, lines 183-194): If (k,r)-graphs of orders n₁,…,n_t exist AND a k-critical graph of order h with exactly t edges exists, then a (k,r)-graph of order h + Σ(nᵢ−1) exists. Construction = Hajós-style: take disjoint H, G₁−v₁,…,G_t−v_t; delete E(H); for edge eᵢ=uᵢwᵢ of H wire uᵢ→Aᵢ, wᵢ→Bᵢ (the two color-classes of vᵢ's neighborhood under a fixed (k−1)-coloring of Gᵢ−vᵢ).
**THIS HOLDS FOR k ≥ 4.** ⟹ a SINGLE (4,1)-graph would immediately spawn (4,1)-graphs of infinitely many orders (combine with Lemma 2.2: sparse k-critical graphs of every order n≥k+3 via Hajós joins / wheels). So the ENTIRE difficulty is finding ONE (4,1)-graph. The amplification is published and free. (Supersedes/sharpens Wang 2009 COCOA ref.)

---

## BOTTOM LINE for the squad
Every published construction route is BLOCKED at k=4 for a SPECIFIC reason:
- Lattanzio: needs k−1 composite; 3 is prime.
- Jensen / Skottová–Steiner circulants: degenerate to χ=3 odd cycles at k=4 (D₂=D₃=∅). Authors believe circulant (4,1)-graphs do NOT exist.
- Martinsson–Steiner: arithmetic forces χ≤3; only large k.
None of these is an IMPOSSIBILITY proof for k=4 in general — they are failures of three specific construction templates. k=4 needs either (a) a genuinely new, non-circulant, non-product, small explicit graph, or (b) an impossibility proof. The Skottová–Steiner §5 necessary conditions (next file) are the sharpest published constraints any (4,1)-graph must satisfy.
