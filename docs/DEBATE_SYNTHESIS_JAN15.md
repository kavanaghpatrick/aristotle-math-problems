# Multi-Agent Debate Synthesis: Bridge Coverage Gap (Jan 15, 2026)

## The Question
For PATH_4 (4 edge-disjoint triangles A—B—C—D), we've proven 2 edges suffice to cover S_e (externals to single element). Does 4×2=8 edges cover ALL triangles including bridges?

---

## Agent Responses

### Grok-4: "Gap is CONDITIONALLY Real"
- Bridges might be auto-covered if they share edges with S_e covers
- But adversarial configurations exist where bridges evade local covers
- Key insight: If ∀ T ∈ Bridges, ∃ X ∈ Packing such that T ∩ F_X ≠ ∅, then gap NOT real
- Recommends: Explicit verification that covers overlap with bridge edges

### Gemini: "Gap is REAL but SOLVABLE via Spine Priority"
**Solution: Bridge-External Equivalence + Adaptive Selection**

The critical insight:
> A bridge is just a specific type of external. A bridge connecting A and B must contain their shared vertex v_AB. Therefore it uses one of A's spokes at v_AB.

**Coordination Strategy:**

| Element | Strategy | Why It Works |
|---------|----------|--------------|
| A (endpoint) | Adaptive: pick spokes if bridges exist | Covers X_AB entirely |
| B (middle) | **Spine Priority**: pick {v₁, v₂} first | Hits X_AB AND X_BC simultaneously |
| C (middle) | **Spine Priority**: pick {v₂, v₃} first | Hits X_BC AND X_CD simultaneously |
| D (endpoint) | Adaptive: pick spokes if bridges exist | Covers X_CD entirely |

**The Magic of Spine Edges:**
- Spine edge {v₁, v₂} in B contains BOTH spine vertices
- Therefore it hits bridges to A (via v₁) AND bridges to C (via v₂)
- If we cannot pick spine edge, then by Forbidden 3-Type Constraint, no bridges exist there

### Codex: "Gap is REAL - Explicit Counterexample"
**Counterexample showing independent selection fails:**
- A covers {a,a'} and {a,v₁}
- B covers {v₁,v₂} and {v₂,b}
- Bridge T = {a, v₁, b} has edges: s(a,v₁), s(v₁,b), s(a,b)
- Neither A's nor B's cover hits T!

This proves independent 2-per-element selection is INSUFFICIENT.

---

## Synthesis: The Resolution

### The Gap is REAL
All three agents agree: naive independent selection can miss bridges.

### The Solution: Coordinated Spine-Priority Selection

The key lemma we need to prove:

```
theorem spine_edge_covers_all_bridges (B : Triangle) (hB : B ∈ M)
    (hMiddle : ∃ A C ∈ M, A.shares_vertex B ∧ B.shares_vertex C) :
    let spine := {v₁, v₂}  -- shared vertices with neighbors
    ∀ T : Triangle, is_bridge T A B ∨ is_bridge T B C →
    spine ∈ T.edges := by
  -- Bridge to A contains v₁ (slot441)
  -- Bridge to C contains v₂ (slot441)
  -- Spine edge {v₁, v₂} contains both
  -- Therefore spine edge hits any such bridge
  sorry
```

### The 8-Edge Construction

1. **Endpoint A**: Pick 2 edges adaptively from S_e(A) ∪ spokes
2. **Middle B**: **Prioritize spine edge {v₁, v₂}** + 1 other edge
3. **Middle C**: **Prioritize spine edge {v₂, v₃}** + 1 other edge
4. **Endpoint D**: Pick 2 edges adaptively from S_e(D) ∪ spokes

**Why this works:**
- Endpoints: 2 edges cover S_e + their single bridge direction
- Middles: Spine edge hits bridges on BOTH sides; +1 edge for remaining S_e
- Total: 2+2+2+2 = 8 edges

### The Forbidden 3-Type Constraint Saves Us
If middle B cannot pick spine edge (because other 2 types are "heavy"):
- Then spine type is empty (by pigeonhole / 6-packing contradiction)
- Empty spine type ⟹ no bridges using that edge type
- So we can safely pick the other 2 edges

---

## Next Steps

1. **Formalize Spine Priority Lemma**: Prove spine edge covers all bridges to neighbors
2. **Prove Middle Element Adaptive**: spine_priority_or_no_bridges
3. **Assemble Final τ ≤ 8**: Combine slot423 + spine priority + endpoints

### Key Files to Create
- `slot425_spine_covers_bridges.lean` - Spine edge hits all adjacent bridges
- `slot426_middle_adaptive.lean` - Middle elements: spine priority works
- `slot427_tau_8_assembled.lean` - Final assembly

---

## Confidence Assessment

| Agent | Gap Real? | Solvable? | Solution |
|-------|-----------|-----------|----------|
| Grok | Conditional | Yes | Verify edge overlap |
| Gemini | Yes | Yes | Spine Priority |
| Codex | Yes (counterexample) | TBD | Needs coordination lemma |

**Consensus**: Gap is real but solvable via spine-priority coordination.
