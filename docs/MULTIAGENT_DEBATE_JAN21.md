# Multi-Agent Debate: Tuza ν=4 Assembly Plan Evaluation

**Date**: 2026-01-21
**Topic**: Does the proposed assembly prove τ ≤ 8?

## The Debate

### Grok-4: PROMISING (with caveats)

**Verdict**: "The assembly logically holds on the surface"

Key points:
- Core logic is sound: maximality → every triangle in some S_e → union of 2-edge covers
- Minor potential gap: S_e definition ambiguity
- Bridge coordination is a moderate concern
- "Promising but needs definitional clarity"

### Gemini: DOES NOT PROVE τ ≤ 8

**Verdict**: "Critical flaws - instance-specific verifications, not general theorems"

Key counterexample:
> If packing triangle m has petals on all 3 edges, τ(S_m) = 3, not 2.

Critical points:
- τ(S_e) ≤ 2 only validated for specific graphs
- `external_has_other_home` proved via `native_decide` on Fin 8
- Proofs are "unit tests that passed", not general theorems

### Codex: INSTANCE-SPECIFIC

**Verdict**: Similar to Gemini - proofs are hardcoded for specific graphs

## The Resolution

### Gemini's Counterexample is Ruled Out by slot412!

`not_all_three_edge_types` (slot412) proves:
> In any graph with ν=4, no packing element can have externals on all 3 edges.

**Proof**: If e has externals T₁, T₂, T₃ on all 3 edges:
- T₁, T₂, T₃ are pairwise edge-disjoint (they use different edges of e)
- T₁, T₂, T₃ are edge-disjoint from B, C, D (by S_e definition)
- Therefore {T₁, T₂, T₃, B, C, D} is a 6-packing
- Contradiction: ν = 4

**Conclusion**: Gemini's "petals on all 3 sides" scenario is impossible when ν=4.

### What's Actually Missing

| Component | Status |
|-----------|--------|
| `not_all_three_edge_types` | ✅ General (slot412) |
| `triangle_shares_edge_with_packing` | ✅ General (slot63) |
| `external_has_other_home` | ⚠️ Instance-specific (slot381) |
| `tau_S_le_2` from 6-packing | ❌ Not explicitly proven |

### The Path Forward

1. **Prove τ(S_e) ≤ 2 from slot412**:
   - "At most 2 edge-types have externals"
   - → Pick one edge per active type (≤ 2 edges)
   - → These 2 edges hit all triangles in S_e

2. **Generalize `external_has_other_home`**:
   - Currently: `native_decide` on Fin 8
   - Need: General proof using maximality

3. **Connect the pieces**:
   - Maximality (general) → Every triangle in some S_e
   - 6-packing (general) → τ(S_e) ≤ 2
   - Union → τ ≤ 8

## Consensus

All three agents agree on one thing: **the proofs need to be general, not instance-specific**.

The key insight from this debate: slot412 (`not_all_three_edge_types`) IS the general theorem that makes τ(S_e) ≤ 2 possible. We just need to explicitly prove the connection.

## Recommended Next Steps

1. Create slot474 with:
   - Import slot412's general theorem
   - Prove: 2 edge-types max → τ(S_e) ≤ 2
   - Use general maximality (not native_decide)
   - Assemble: 4 × 2 = 8

2. Submit to Aristotle for gap-filling

3. Re-audit with all three agents
