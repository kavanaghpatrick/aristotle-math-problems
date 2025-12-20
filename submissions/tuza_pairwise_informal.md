# Tuza's Conjecture: Pairwise Descent for ν=4

## Known Results

1. **τ(S_e) ≤ 2**: Triangles sharing edge with e but not with other packing elements can be covered by 2 edges.

2. **τ(X(e,f)) ≤ 2**: When packing elements e and f share exactly one vertex v, all triangles in T_e ∩ T_f contain v and can be covered by 2 edges incident to v.

3. **Inductive bound**: τ(G) ≤ τ(T_e) + τ(G \ T_e)

## The ν=4 Gap

Parker's approach fails at ν=4 because for every e in a maximum packing, T_e ⊃ S_e (strict containment). In the K_6 configuration with 4 edge-disjoint triangles, τ(T_e) = 3 for all e, giving bound 3 + 6 = 9 instead of required 8.

## Pairwise Descent Strategy

**Key Insight**: Instead of removing one triangle at cost τ(T_e), remove a PAIR {e, f} that share a vertex.

**Claim**: τ(T_e ∪ T_f) ≤ 4 when e ∩ f = {v}.

**Proof Sketch**:
- T_e ∪ T_f decomposes into: S_e (private to e), S_f (private to f), X(e,f) (shared)
- All triangles in X(e,f) contain the shared vertex v
- Cover X(e,f) using 2 edges incident to v (from e or f)
- These same edges partially cover S_e and S_f
- Complete the cover of S_e with at most 1 additional edge
- Complete the cover of S_f with at most 1 additional edge
- Total: ≤ 4 edges

**Why this works in K_6**:
In K_6 with packing {e₁, e₂, e₃, e₄}, pick any pair e₁, e₂ sharing vertex v.
- τ(T_{e₁} ∪ T_{e₂}) ≤ 4
- Residual has ν ≤ 2
- τ(residual) ≤ 4 by known ν ≤ 2 result
- Total: 4 + 4 = 8 ✓

## Theorem to Prove

For ν = 4: τ(G) ≤ 8

**Case Analysis**:

Case A: ∃ e ∈ M isolated (shares no vertex with other packing elements)
- Then T_e = S_e, so τ(T_e) ≤ 2
- Use standard induction: τ ≤ 2 + 2(3) = 8 ✓

Case B: Every e shares a vertex with some other f
- Pick any such pair {e, f}
- τ(T_e ∪ T_f) ≤ 4
- Residual has ν ≤ 2, so τ(residual) ≤ 4
- Total: τ ≤ 4 + 4 = 8 ✓
