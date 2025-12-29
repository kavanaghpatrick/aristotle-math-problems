# Alternative Proof Strategies Debate
**Date**: 2025-12-25
**Question**: Are we being too narrow with S_e decomposition and All-Middle partition?

---

## Gemini's Alternative Approaches

### 1. SAT/SMT Counterexample Search
**Idea**: Instead of proving τ ≤ 8, try to DISPROVE it using constraint solvers.

**Implementation**:
- Model cycle_4 configuration with N vertices (12-15)
- Hard constraints: Packing edges form cycle_4 triangles
- Maximality: No other edge-disjoint triangle exists
- Target: Assert τ(G) > 8 (every 8-edge subset leaves a surviving triangle)

**Why valuable**: If UNSAT for small graphs → no counterexample exists → structural insight

### 2. LP Dual / Type-Analysis
**Idea**: Classify triangles by intersection signature with packing.

**Triangle Types**:
- Type 1: Intersects only T_A
- Type 2: Intersects T_A and T_B (bridge)
- Type 3: Intersects T_A and T_C (diagonal - the villain)
- Type 4: Intersects 3+ packing triangles

**Approach**: Assign costs to edges, formulate LP, prove weighted solution ≤ 8.

### 3. Vertex-Centric Heavy/Light Analysis
**Current**: Edge-centric (S_e, T_pair)
**Alternative**: Group by packing VERTICES, not edges.

**Strategy**:
- Heavy vertex (high degree): Picking incident edges is efficient
- Light graph (all sparse): Easy to cover
- Analyze "corner vertices" of cycle_4

---

## Codex's Alternative Approaches (5 strategies)

### 1. Iterative LP/ILP Rounding
**Key insight**: For ν = 4, every basic feasible dual solution uses ≤ 4 constraints, so at most 6 edges can be tight.

**Method**:
1. Solve LP: minimize Σ y_e s.t. Σ_{e∈Δ} y_e ≥ 1
2. Lock edges with y_e ≥ 1
3. Residual has ≤ 6 edges → brute-force ILP (2^6 = 64 cases)
4. Splice solutions → τ ≤ 8

### 2. Sherali-Adams Lift-and-Project
**Key insight**: LP optimal is 4 (dual = ν), so Σ y_e ≤ 8 fractionally.

**Method**:
- Order-2 SA lift forces y_e ∈ {0, 1/2, 1}
- Every triangle hits packing → at most 2 half-edges per packing edge
- Contract packing edges → 3-uniform hypergraph with τ ≤ 2
- Round half-integers by pairing

### 3. Minimal Counterexample + Discharging
**Assume**: G is minimal with ν = 4 but τ ≥ 9.

**Extremal properties**:
- δ(G) ≥ 4
- Every edge lies in a triangle
- G is 3-connected

**Attack**: Build link graphs L_v. Each is C₅ or has matching ≥ 3.
Use discharging: prove ∃ vertex v with L_v having τ ≤ 2.
Delete v → contradiction with minimality.

### 4. SAT Obstruction Enumeration
**Encoding**: "G has ν = 4, τ ≥ 9, |V| ≤ 10"

**Variables**:
- x_{uv}: edge existence
- Packing constraints
- 8 selector variables for hitting set

**Result**: UNSAT → counterexample needs > 10 vertices
SAT certificates → new structural rules

### 5. Hypergraph Transversal Reduction
**Transform**: G → 3-uniform hypergraph H
- Vertices of H = edges of G
- Hyperedges of H = triangles

**Apply**: Aharoni-Haxell theorem for rank-3 hypergraphs with max pair-degree ≤ 3: τ(H) ≤ 2ν(H)

**Show**: Minimal counterexample reduces to bounded pair-degree hypergraph.

---

## Synthesis: Approaches We're Missing

| Approach | Source | Effort | Potential |
|----------|--------|--------|-----------|
| **SAT Verification** | Gemini + Codex | Low | High - ground truth |
| **LP Rounding** | Codex | Medium | High - bypasses structure |
| **Vertex-Centric** | Gemini | Medium | High - different perspective |
| **Discharging** | Codex | High | High - standard tool |
| **Hypergraph Reduction** | Codex | High | Medium - reframing |
| **Type Classification** | Gemini | Low | Medium - cleaner structure |

---

## Recommended Priority

### Immediate (Low effort, high value)
1. **SAT Encoding**: Build Z3/SAT script for cycle_4 with |V| ≤ 12
   - If UNSAT: No small counterexample → structural insight
   - If SAT: Found counterexample → revise approach

2. **Type Classification**: Enumerate triangle types for cycle_4
   - How many Type 3 (diagonal) triangles can exist?
   - What constraints do they impose?

### Medium Term (Pivot if current fails)
3. **LP Rounding**: Implement iterative rounding
   - Residual LP has ≤ 6 edges
   - Brute-force small ILP

4. **Vertex-Centric**: Analyze corner vertices of cycle_4
   - What happens if we cover one corner?
   - Does the problem reduce?

### Formal Verification
5. **Minimal Counterexample + Discharging**: Classical proof technique
   - Requires more Lean infrastructure
   - But avoids all our current gaps

---

## Key Insight

**We ARE too narrow.** All our current approaches share a common structure:
- Decompose triangles by packing edges
- Bound τ for each piece
- Sum up

**The alternatives suggest**:
- Don't decompose → use LP globally
- Decompose by VERTICES, not edges
- Don't prove → verify small cases with SAT
- Assume counterexample exists → derive contradiction

---

## Action Items

1. [ ] Build SAT encoder for cycle_4 verification
2. [ ] Classify triangle types for cycle_4 structure
3. [ ] Implement vertex-centric analysis
4. [ ] Research Aharoni-Haxell applicability
5. [ ] Continue S_e decomposition (slot74b) as parallel track

**The SAT approach is the fastest way to either confirm our direction or find a counterexample we missed.**
