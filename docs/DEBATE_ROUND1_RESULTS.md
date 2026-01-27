# Round 1 Results: Multi-Agent Debate on τ ≤ 8 for PATH_4

**Date**: 2026-01-15
**Participants**: Gemini, Opus Task Agent (Grok unavailable due to API timeout)

---

## Agent 1: Gemini

### Proposal: Constructive Conditional Selection

**Endpoint Coverage (A and D):**
- Cannot use fixed selection; must use conditional selection based on which external types exist
- For A = {v₁, a₂, a₃}:
  - **Case 1**: Type a₂-a₃ (Base) is Empty
    - Selection: {s(v₁, a₂), s(v₁, a₃)} (both spokes)
    - Covers all S_e externals and A-B bridges (both edges contain v₁)
  - **Case 2**: Type a₂-a₃ is Non-Empty
    - By `not_all_three_edge_types`, one spoke type must be empty
    - **Subcase 2a**: Type v₁-a₂ empty → Selection: {s(a₂, a₃), s(v₁, a₃)}
    - **Subcase 2b**: Type v₁-a₃ empty → Selection: {s(a₂, a₃), s(v₁, a₂)}

**Bridge Coverage:**
- **Risk identified**: In Case 2a, selection {s(a₂, a₃), s(v₁, a₃)} misses edge {v₁, a₂}
- If a bridge uses {v₁, a₂} from A, A fails to cover it → must guarantee B covers it
- **Proposed solution**: B should use {s(v₁, v₂), s(v₁, b₃)} to cover all B-edges incident to v₁
- **Remaining concern**: "Double Miss" scenario where both A and B miss the same bridge

**Approach**: Constructive Case Split
**Confidence**: 80%
**Risk**: Need to prove "bad cases" for A and B cannot occur simultaneously

---

## Agent 2: Opus Task Agent

### Proposal: Two-Phase Existential Approach

**Endpoint Coverage (A and D):**
- Use proven `exists_two_edges_cover_Se` directly without explicit construction
- For each endpoint, apply the existence lemma to get witnesses e₁, e₂
- Selection is existential - we don't specify which 2 edges, only that they exist

**Bridge Coverage:**
Key insight: **Bridges are NOT in S_e by definition**
- An X_{A,B} bridge T satisfies |T ∩ B| ≥ 2, violating S_e definition's condition 3
- Therefore bridges need separate handling

**Bridge Coverage Strategy:**
- Every X_{A,B} bridge contains v₁ (by `bridge_contains_shared`)
- **Key observation**: Any 2-edge selection from a triangle's 3 edges MUST include at least one spoke
  - Edges of A: {s(v₁, a₂), s(v₁, a₃), s(a₂, a₃)}
  - Only s(a₂, a₃) doesn't contain v₁
  - Any 2-edge selection includes at least one of s(v₁, a₂) or s(v₁, a₃)
- **Therefore**: A's selection always covers bridges containing v₁ and either a₂ or a₃

**Approach**: Existential (with constructive bridge handling)
**Confidence**: 70%
**Risk**: Needs verification that `exists_two_edges_cover_Se` returns edges from E.edges only

---

## Synthesis: Key Points of Agreement and Disagreement

### Agreement
1. **Middle elements are solved** via `middle_no_base_externals`
2. **Bridges require separate handling** - not covered by S_e lemma
3. **`not_all_three_edge_types` is key** - ensures 2 edges suffice for endpoints
4. **Bridge forcing via spokes** - any 2-edge selection includes a v₁-spoke

### Disagreement
1. **Constructive vs Existential**: Gemini prefers explicit case split; Opus prefers using existence directly
2. **Bridge coordination**: Gemini identifies potential "double miss"; Opus argues it's structurally impossible

### Critical Open Question
**Can a "Double Miss" occur?**
- Bridge T uses {v₁, a₂} from A (missed by A in Case 2a) AND uses {v₁, b₃} from B
- This requires A to have base externals AND B to have certain external pattern
- Need to verify if this configuration is ruled out by ν=4 constraint

---

## Round 2 Questions

1. **For Gemini**: Can you prove the "Double Miss" is impossible? What structural property rules it out?

2. **For Opus**: The proof of `exists_two_edges_cover_Se` in slot422 - does it guarantee both edges are from E's own edges? If e₂ can be any graph edge, does your spoke argument still hold?

3. **For Both**: What is the simplest Lean formalization? Should we:
   - Define the cover via cases (Gemini's approach)
   - Use Choice on existence lemma (Opus's approach)
   - Prove a stronger intermediate lemma (e.g., "endpoint selection always includes spine-spoke")

---

## Moderator Notes

**From DB analysis:**
- 38 files fully proven (0 sorry)
- slot407 claims tau_le_8_path4 PROVEN - need to verify validity
- Near-misses: slot571 (1 sorry), slot565 (1 sorry, 15 proven)

**Known blockers:**
- `sym2_cover_cardinality` is FALSE - never use A.sym2 for edge enumeration
- Bridge externals do NOT share common apex across M-elements

**Recommendation for Round 2:**
Focus on the "Double Miss" scenario. If we can rule it out, both approaches converge.
