# Tuza Conjecture: Complete Research Context for AI Consultation

## The Conjecture
**Tuza (1990)**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles (covering number)
- ν(G) = maximum edge-disjoint triangles (packing number)

## Current Frontier
**Parker (2025)** proved Tuza for ν ≤ 3. The **ν = 4 case is OPEN**.

---

## PROVEN LEMMAS (Machine-Verified in Lean 4)

### Parker Lemmas (10 proven)
| Lemma | Statement | Proof Technique |
|-------|-----------|-----------------|
| `lemma_2_2` | S_e triangles pairwise share edges | Maximality contradiction |
| `lemma_2_3` | ν(G \ T_e) = ν - 1 | M \ {e} is valid packing |
| `inductive_bound` | τ(G) ≤ τ(T_e) + τ(G \ T_e) | Union of covers |
| `covering_number_le_two_of_subset_four` | Triangles on ≤4 vertices: τ ≤ 2 | Case analysis |
| `intersecting_family_structure` | Pairwise edge-sharing → Star OR K4 | 3 triangles force 4 vertices |
| `tau_star` | Star has τ ≤ 1 | Common edge covers all |
| `tau_S_le_2` | τ(S_e) ≤ 2 always | Combines star/K4 structure |

### Additional Proven (10 more)
| Lemma | Statement |
|-------|-----------|
| `Te_eq_Se_union_bridges` | T_e = S_e ∪ bridges decomposition |
| `tau_Te_le_2_nu_1` | For ν=1, τ(T_e) ≤ 2 |
| `edge_disjoint_share_le_1` | Edge-disjoint triangles share ≤1 vertex |
| `bridge_shares_with_le_2` | Bridge shares with ≤2 packing elements (ν=3) |
| `exists_petal_of_edge` | Each edge has petal when τ(S_e) > 2 |
| `common_petal_vertex` | Adjacent edge petals share external vertex |
| `tuza_nu0`, `tuza_nu1`, `tuza_nu2` | Base cases proven |

### Key Definitions
```lean
def S_e := triangles sharing edge with e but NOT sharing edge with other M elements
def bridges := T_e \ S_e = triangles connecting e to other packing elements
def T_e := all triangles sharing an edge with packing element e
```

---

## COUNTEREXAMPLES FOUND (Flawed Strategies Disproven)

| Strategy | Counterexample | Insight |
|----------|----------------|---------|
| `TuzaReductionProperty` | 2 triangles sharing edge | Edge reduction doesn't preserve τ ≤ 2ν |
| `two_edges_cover_nearby` | K4 | 2 edges of e insufficient for pairwise-sharing |
| `pairwise_sharing_covered_by_e` | K4 on Fin 4 | Need external edges, not just e's edges |

---

## LITERATURE BOUNDS (Constraints on Counterexamples)

### Counterexample MUST satisfy:
| Constraint | Source | What it rules out |
|------------|--------|-------------------|
| mad(G) ≥ 7 | Puleo 2015 | Sparse graphs |
| χ(G) ≥ 5 | Lakshmanan 2012 | 4-colorable graphs |
| treewidth ≥ 7 | Botler 2020 | Low treewidth |
| NOT tripartite | Haxell-Kohayakawa 1998 | Tripartite graphs |
| NOT 4-partite | Lakshmanan 2012 | k-partite for k≤4 |
| NOT odd-wheel-free | Lakshmanan 2012 | Odd-wheel-free |
| NOT random | Kahn-Park 2022 | Random graphs |
| NOT K4-free planar | Various | K4-free planar |
| NOT threshold | Threshold 2021 | Threshold graphs |

### Best General Bounds:
- τ ≤ (66/23)ν ≈ 2.87ν (Haxell 1999) - best known
- τ ≤ 3ν (trivial greedy) - we proved this
- τ ≤ 2ν* (Krivelevich 1995) - fractional
- τ ≤ 2ν* - (1/√6)√ν* (Chapuy 2014) - improved fractional

### Fractional Theory:
- τ* = ν* (LP duality, Krivelevich 1995)
- τ ≥ τ* = ν* ≥ ν (chain)
- Tuza ⟺ integrality gap ≤ 2

---

## ν=4 SPECIFIC ANALYSIS

### Why Parker Fails at ν=4:
At ν ≤ 3: Can guarantee some e ∈ M has τ(T_e) ≤ 2
At ν = 4: Bridges can attach to 3 elements, breaking τ(T_e) ≤ 2 guarantee

### Key Gap:
**Need**: τ(T_e ∪ T_f) ≤ 4 when e ∩ f = {v}
**Have**: τ(S_e) ≤ 2, τ(S_f) ≤ 2, but bridges complicate union

### Induction Formula:
τ ≤ τ(T_e ∪ T_f) + 2(ν - 2)
For ν=4: τ ≤ τ(T_e ∪ T_f) + 4
Need τ(T_e ∪ T_f) ≤ 4 to get τ ≤ 8

---

## GENUINELY OPEN PROBLEMS (Not Just Formalization)

### Tier 1: Direct Extensions
1. **ν = 4 case** - Completely open, our main target
2. **ν = 5, 6, ...** - All open beyond Parker's ν ≤ 3
3. **Tightness at ν=4** - Does any graph achieve τ = 8 with ν = 4?

### Tier 2: Bound Improvements
4. **Better than 2.87** - Can we prove τ ≤ 2.5ν?
5. **Asymptotic tightness** - Is τ/ν → 2 as ν → ∞?

### Tier 3: Related Open Problems
6. **Split Graphs** - General case open (only threshold subset solved)
7. **Aharoni-Zerbib generalization** - r-uniform hypergraphs: τ/ν ≤ ⌈(r+1)/2⌉

### Tier 4: Meta-Questions
8. **Counterexample existence** - Does one exist? (Most believe NO)
9. **Integrality gap** - Prove τ ≤ 2τ* directly

---

## CURRENT ARISTOTLE SUBMISSIONS (ν=4 Portfolio)

| Slot | UUID | Strategy | Target |
|------|------|----------|--------|
| 1 | 78321b54 | Scaffolded | tau_union_le_4 |
| 2 | 7cd92201 | Boris Minimal | base_camp_nu2 |
| 3 | d9cf0918 | Fractional | LP duality |
| 4 | d9a944e6 | Scaffolded | bridges |
| 5 | 8ea799df | Scaffolded | dense_core |
| 6 | 226432ff | Heavy Scaffold | parker_integration |
| 7 | 51a69672 | Boris Minimal | pure exploration |

---

## SUMMARY STATISTICS
- **Papers indexed**: 15
- **Lemmas extracted**: 63
- **Lemmas proven (machine-verified)**: 30
- **Counterexamples found**: 3
- **Submissions running**: 7
