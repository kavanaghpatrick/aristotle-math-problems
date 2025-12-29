# Round 1 Debate Synthesis

## Models Consulted
- **Gemini**: Full analysis via CLI
- **Codex**: Full analysis via agent
- **Grok**: API timeout (excluded)

## CONSENSUS

### Path A (Local Tuza) is the correct approach

Both Gemini and Codex agree:
1. Path B (Diagonal Pairing) relies on potentially false lemmas
2. Path A has proven infrastructure (local_tuza_via_link_graph)
3. The S_e structure approach is sound

### Key Disagreement: packing_sum_le_global

| Model | Verdict | Reasoning |
|-------|---------|-----------|
| Gemini | TRUE (effectively) | Bridge absorption makes it work |
| Codex | FALSE (naive form) | Packings can share edges across partitions |

**Resolution**: Use Bridge Absorption approach - don't assume naive packing sum, but prove bridges are covered by S_e covers.

## PRIORITY ORDER FOR SUBMISSIONS

### Priority 1: cycle4_all_triangles_contain_shared
Every triangle contains at least one shared vertex {v_ab, v_bc, v_cd, v_da}.

**Proof strategy**:
1. By maximality, triangle t shares edge with packing element X
2. Each packing element has exactly 2 shared vertices
3. Any edge of X contains at least one shared vertex
4. Therefore t contains shared vertex

### Priority 2: Bridge Absorption Lemma
If t ∈ X_AB (bridge between A and B), then t is already covered by S_A's cover.

**Proof strategy** (Gemini):
- Bridge t = {v_ab, a, b} where a ∈ A, b ∈ B
- S_A's "star" structure must be centered at vertex outside A
- The only such vertex in t is b
- Therefore S_A's cover uses edges at b, which hits t

### Priority 3: Direct 8-Edge Construction
Construct explicit cover: spokes from each shared vertex to adjacent privates.

**Cover** (Codex):
```
{v_ab-a_priv, v_ab-b_priv, 
 v_bc-b_priv, v_bc-c_priv, 
 v_cd-c_priv, v_cd-d_priv, 
 v_da-d_priv, v_da-a_priv}
```

### Priority 4: diagonal_bridges_empty
X_AC = X_BD = ∅ (no bridges between diagonal elements)

## RECOMMENDED ARISTOTLE SUBMISSIONS

### Slot A: cycle4_all_triangles_contain_shared
Single-sorry at target lemma, all dependencies proven.

### Slot B: bridge_absorption
Single-sorry at bridge absorption lemma.

### Slot C: tau_le_8_direct_construction
Prove τ ≤ 8 by explicit 8-edge cover construction.

## POTENTIAL FIX NEEDED

Gemini identified that `slot71_5a800e22/Se_structure.lean` has an `exact?` placeholder:
```lean
-- Line 125, replace with:
exact S_e_cross_intersect G M hM e he t1 t2 ht1 ht2 ht1_ne_e ht2_ne_e h_diff_edges
```

## NEXT STEPS

1. Check if slot71 fix is needed
2. Create single-sorry submission files
3. Submit in parallel to Aristotle
