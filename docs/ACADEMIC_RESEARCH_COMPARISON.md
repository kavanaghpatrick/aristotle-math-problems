# Academic Research Comparison — Our Proven Lemmas vs Literature

**Date**: February 8, 2026
**Source**: Parallel research by 3 agents across web, arxiv, Mathlib, AFP, Coq libraries

---

## EXECUTIVE SUMMARY

### Our Work is at the Exact Frontier

| Finding | Detail |
|---------|--------|
| **ν ≤ 3 JUST proven** | Parker (2024/2025) proved Tuza for ν ≤ 3. **ν = 4 is the smallest open case.** |
| **No formal verification exists** | No proof assistant (Lean/Coq/Isabelle) has ANY case of Tuza formalized — not even the statement |
| **No AI prover has tried Tuza** | We are the first to apply AI-assisted proof search to triangle packing/covering |
| **Mathlib lacks definitions** | `trianglePackingNumber` and `triangleCoveringNumber` don't exist in Mathlib |
| **Best general bound: τ ≤ 2.87ν** | Haxell (1999) gives τ ≤ 11 for ν=4 — far from our target τ ≤ 8 |

**Bottom line: Proving τ ≤ 8 for ν = 4 would be a publishable result in combinatorics, and formally verifying it in Lean would be a first-of-its-kind achievement.**

---

## 1. KEY REFERENCE: Parker (2024/2025)

**"New bounds on a generalization of Tuza's conjecture"**
- [arXiv:2406.06501](https://arxiv.org/abs/2406.06501)
- [Electronic Journal of Combinatorics, v32i2p20](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i2p20)

Parker proves Tuza for ν ≤ 3 via the Aharoni-Zerbib generalization. Key overlap with our work:

| Our Concept | Parker Equivalent | Status |
|-------------|-------------------|--------|
| S_e (externals of e) | Definition 2.1 | **KNOWN** |
| S_e disjointness | Lemma 2.2 | **KNOWN** |
| ν(S_e) = 1 | Lemma 2.2 consequence | **KNOWN** |
| S_e apex/star structure | Lemma 2.6 (for ν=1 case) | **KNOWN** (restricted form) |
| Triangle classification (M / external / bridge) | Implicit in Def 2.1 | **KNOWN** |
| S_e dichotomy (common edge OR common apex) | Not in this form | **NOVEL formulation** |

**Critical**: Parker works in k-uniform hypergraph setting. Our graph-specific formulations + formal proofs are distinct contributions.

---

## 2. NOVELTY ASSESSMENT OF OUR PROVEN LEMMAS

### NOVEL (Not in Literature)

| Lemma | Why Novel |
|-------|----------|
| **S_e structure dichotomy** | "Common edge subset of e OR common external vertex" — this specific formulation is new |
| **All formal verifications** | First-ever Lean 4 proofs for ANY Tuza structural results |
| **"Bridge triangle" classification** | Terminology and systematic treatment are ours |
| **Exhaustive 11-pattern classification** (slot466) | Specific to ν=4, not published |
| **τ ≤ 4 for star_all_4, three_share_v, scattered, two_two_vw, cycle_4** | Concrete ν=4 case results, formally verified |
| **middle_no_base_externals** | PATH_4 specific structural result |
| **bridge_spine_covers_all_bridges** | PATH_4 specific covering result |
| **not_all_three_edge_types** | 6-packing contradiction lemma |

### FOLKLORE (Known but Not Published Standalone)

| Lemma | Status |
|-------|--------|
| **τ(S_e) ≤ 2** | Follows from Parker's ν(S_e)=1; not published as standalone |
| **Local Tuza via link graph** (τ(T_v) ≤ 2·ν(T_v)) | Standard König reduction; first formal proof is ours |
| **Bridge containment** (bridges contain shared vertex) | Elementary consequence of edge-disjointness |
| **τ(X_ef) ≤ 2** for bridges | Similar reasoning to τ(S_e) ≤ 2 |
| **Avoiding triangles share base edge** | Elementary observation |

### KNOWN (Published)

| Lemma | Reference |
|-------|-----------|
| `triangle_shares_edge_with_packing` | Standard maximality property |
| `packing_inter_le_one` | Definition of edge-disjoint packing |
| `tau_union_le_sum` (subadditivity) | Standard |
| `krivelevich_tau_le_2nu_star` | Krivelevich (1995) |
| `vertex_cover_le_two_matching` | König-type, classical |
| `exists_maximal_matching` | Standard greedy argument |
| `helly_triangles_edges` | Helly property |

---

## 3. FALSIFIED RESULTS — ALSO VALUABLE

| What We Disproved | Significance |
|-------------------|-------------|
| **Apex approach** (slot542/543) | Showed bridge_has_apex_in_bridge is FALSE on Fin 11 |
| **same_edge_share_external_vertex** (slot252) | Counterexample on concrete graph |
| **Propeller 4-packing invalid** (slot57) | Not a valid maximal packing |
| **39 false lemmas total** | Systematic falsification catalog — no comparable resource exists |

These negative results are publishable contributions: they document blind alleys.

---

## 4. COMPARISON WITH BEST KNOWN BOUNDS

| Result | Source | ν=4 Implication |
|--------|--------|-----------------|
| τ ≤ (66/23)ν ≈ 2.87ν | Haxell (1999) | τ ≤ 11 |
| τ ≤ 2ν* | Krivelevich (1995) | τ ≤ 8 (if ν* = 4) |
| τ ≤ 2ν for ν ≤ 3 | Parker (2024) | Does NOT cover ν=4 |
| τ ≤ 2ν for avg degree < 7 | Puleo (2015) | Only sparse graphs |
| **τ ≤ 8 for ν = 4 (all graphs)** | **US (in progress)** | **Would be NEW** |

---

## 5. WHAT CONSTITUTES A PUBLISHABLE CONTRIBUTION

### Tier 1: Breakthrough (Top Journal)
- **τ ≤ 8 for all graphs with ν = 4** — general theorem on SimpleGraph V
- Extends Parker's ν ≤ 3 to ν ≤ 4

### Tier 2: Strong Contribution (Good Journal)
- **τ ≤ 8 for ν = 4 verified on Fin n** — concrete but not general
- First formal verification of Tuza structural results
- AI-assisted proof methodology paper

### Tier 3: Workshop/Note
- Individual structural lemmas (S_e structure, fan structure, etc.)
- False lemma catalog
- Aristotle capability taxonomy for combinatorics

---

## 6. GAPS TO CLOSE

### Mathematical Gaps
1. **PATH_4 τ ≤ 8 general**: Currently only τ ≤ 10 (general) or τ ≤ 8 (Fin n)
2. **Classification transfer**: Show every maximal 4-packing maps to one of 11 patterns on general V
3. **Assembly**: Chain case-by-case results into universal theorem

### Formalization Gaps
1. **SimpleGraph V formulation**: Current proofs use Fin n, need arbitrary V
2. **Mathlib infrastructure**: Need to define `trianglePackingNumber` and `triangleCoveringNumber`
3. **Import coherence**: Reconcile with current Mathlib version

---

## 7. RECENT PAPERS TO STUDY IN DETAIL

| Paper | Year | Why Relevant |
|-------|------|-------------|
| [Parker: New bounds on Tuza generalization](https://arxiv.org/abs/2406.06501) | 2024 | **CRITICAL** — closest work, proves ν ≤ 3 |
| [Kahn, Park: Tuza for random graphs](https://onlinelibrary.wiley.com/doi/abs/10.1002/rsa.21057) | 2022 | Probabilistic methods |
| [Bozyk et al.: Tuza for threshold graphs](https://arxiv.org/abs/2105.09871) | 2022 | Graph class approach |
| [Chalermsook et al.: Multi-transversals](https://arxiv.org/abs/2001.00257) | 2020 | Charging arguments |
| [Pudelko, Ruf: Triangulations + treewidth](https://arxiv.org/abs/2002.07925) | 2020 | τ ≤ 3/2·ν for planar |
| [Aristotle paper](https://arxiv.org/abs/2510.01346) | 2025 | AI prover methodology |

---

## 8. ACADEMIC CONTEXT FOR FORMAL VERIFICATION

### What HAS Been Formalized in Extremal Combinatorics
- Szemerédi Regularity Lemma (Lean 4 + Isabelle, 2022)
- PFR Conjecture (Lean 4, 2023 — 3 weeks after proof announced)
- Diagonal Ramsey improvement (Isabelle, 2024)
- Triangle Removal Lemma (Lean 4, in Mathlib)
- Turán's theorem (Lean 4, in Mathlib)

### What Has NOT Been Formalized
- Any triangle packing/covering result
- Any case of Tuza's conjecture
- König's theorem in full generality (though matching theory is developing)
- LP duality for combinatorial optimization

**Our project would be the first formalization in the triangle packing/covering space.**

---

## RECOMMENDED NEXT STEPS

1. **Read Parker (2024) in detail** — understand exactly where ν ≤ 3 proof fails for ν = 4
2. **Determine if Parker's hypergraph framework can be extended** — his Lemma 2.2, 2.6, 2.7 may provide scaffold
3. **Focus on PATH_4 τ ≤ 8** — this is the critical remaining case
4. **Consider publishing intermediate results** as a "case analysis + formal verification" paper
5. **Explore contributing Tuza definitions to Mathlib** — `trianglePackingNumber`, `triangleCoveringNumber`
