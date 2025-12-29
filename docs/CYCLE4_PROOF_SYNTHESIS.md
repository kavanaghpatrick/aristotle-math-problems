# Cycle_4 Proof Synthesis: Complete Strategy

> ## ⚠️ CRITICAL WARNING (December 26, 2025)
>
> **THIS DOCUMENT IS OBSOLETE.** Key lemma `local_cover_le_2` referenced below
> is **MATHEMATICALLY FALSE** (Codex counterexample - 4 edges may be required, not 2).
>
> **DO NOT USE** the strategy described here.
>
> **SEE INSTEAD**:
> - `docs/FALSE_LEMMAS.md` - Full explanation of why it's false
> - `docs/ATTACK_PLAN_15_SLOTS.md` - Corrected strategy using "support clusters"
> - `docs/AI_DEBATE_DEC26.md` Round 9 - Codex's counterexample

**Date**: 2025-12-25
**Status**: ~~ALL KEY LEMMAS NOW PROVEN~~ **INVALIDATED** - local_cover_le_2 is FALSE

---

## Breakthrough: Classification Lemma ALREADY PROVEN

In `proven/tuza/nu4/slot71_5a800e22/Se_structure.lean`, Aristotle proved:

```lean
lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ ∀ t ∈ S_e G M e, t ≠ e → {u, v} ⊆ t) ∨
    (∃ x : V, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t)
```

**This is exactly the Classification Lemma!** It says:
- **Case 1**: All S_e triangles share a common edge {u,v} of e → τ(S_e) = 1
- **Case 2**: All S_e triangles share a common external vertex x → τ(S_e) ≤ 2 (via spokes from x)

---

## Complete Inventory of Proven Lemmas

### Core Infrastructure (slot71)
| Lemma | English | τ Bound |
|-------|---------|---------|
| `tau_union_le_sum` | τ(A ∪ B) ≤ τ(A) + τ(B) | Subadditivity |
| `S_e_pairwise_intersect` | S_e triangles share ≥2 vertices | Structure |
| `S_e_structure` | S_e = star OR external vertex | τ(S_e) ≤ 2 |

### Cycle_4 Specific (slot73)
| Lemma | English |
|-------|---------|
| `cycle4_all_triangles_contain_shared` | ALL-MIDDLE: Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da |
| `cycle4_no_loose_triangles` | Every triangle shares edge with some packing element |
| `local_cover_le_2` | At shared vertex v, 2 edges of M suffice for triangles at v |

### Additional (slot70)
| Lemma | English |
|-------|---------|
| `diagonal_bridges_empty` | X_AC = X_BD = ∅ in cycle_4 |

---

## The Complete Proof Strategy

### Step 1: Partition by S_e
Every triangle shares edge with exactly one or more packing elements:
- T = S_A ∪ S_B ∪ S_C ∪ S_D ∪ X_AB ∪ X_BC ∪ X_CD ∪ X_DA ∪ X_AC ∪ X_BD

### Step 2: Eliminate Diagonal Bridges
By `diagonal_bridges_empty`:
- X_AC = ∅
- X_BD = ∅

### Step 3: Bound S_e Sets
By `S_e_structure`:
- τ(S_A) ≤ 2 (either common edge OR common external vertex)
- τ(S_B) ≤ 2
- τ(S_C) ≤ 2
- τ(S_D) ≤ 2

**Total from S_e: ≤ 8 edges**

### Step 4: Handle Adjacent Bridges
For X_AB (bridges between A and B):
- By `bridges_contain_shared_vertex`: All X_AB triangles contain v_ab
- X_AB triangles share edges with BOTH A and B
- These edges include edges of A and B at v_ab

**Key Observation**: X_AB triangles are ALREADY covered by S_A ∪ S_B edges!

Why? If t ∈ X_AB:
- t shares edge with A at v_ab (one of A's edges at v_ab)
- The S_A cover includes this edge (by S_e_structure)
- Therefore t is already hit!

### Step 5: Assembly
| Set | Bound | Absorbed? |
|-----|-------|-----------|
| S_A | ≤ 2 | No |
| S_B | ≤ 2 | No |
| S_C | ≤ 2 | No |
| S_D | ≤ 2 | No |
| X_AB | ≤ 2 | YES - by S_A ∪ S_B cover |
| X_BC | ≤ 2 | YES - by S_B ∪ S_C cover |
| X_CD | ≤ 2 | YES - by S_C ∪ S_D cover |
| X_DA | ≤ 2 | YES - by S_D ∪ S_A cover |
| X_AC | 0 | EMPTY |
| X_BD | 0 | EMPTY |

**Total: τ ≤ 4 × 2 = 8**

---

## Remaining Lemma: Bridge Absorption

The one piece we still need to prove formally:

```lean
lemma bridge_absorbed_by_S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (E_A : Finset (Sym2 V)) (hE_A : covers E_A (S_e G M A))
    (E_B : Finset (Sym2 V)) (hE_B : covers E_B (S_e G M B)) :
    covers (E_A ∪ E_B) (X_ef G A B)
```

**Proof sketch**:
1. Let t ∈ X_AB. Then t shares edge with both A and B.
2. t contains v (by bridges_contain_shared_vertex).
3. The edge t shares with A is one of A's edges at v.
4. By S_e_structure for A:
   - Either all S_A triangles share a common edge of A (which includes this edge)
   - Or all S_A triangles share common vertex outside A
5. In case 1: E_A contains this edge → E_A hits t.
6. In case 2: Need to show t shares vertex with some S_A triangle → uses the "pairwise intersect" property.

Actually, wait - X_AB triangles are NOT in S_A (they share with B too). So the absorption is more subtle.

---

## Alternative: Per-Vertex Assembly

Instead of per-S_e, we can use per-shared-vertex:

At v_ab:
- All triangles containing v_ab must share edge with A or B (by maximality + diagonal_bridges_empty)
- By `local_cover_le_2`: 2 edges at v_ab suffice

Similarly for v_bc, v_cd, v_da.

Total: 4 × 2 = 8.

**This approach ALREADY WORKS with `local_cover_le_2`!**

---

## Path to Completion

### Option A: Use existing `local_cover_le_2`
1. Apply `cycle4_all_triangles_contain_shared` to partition by shared vertex
2. Apply `local_cover_le_2` at each shared vertex
3. Apply `tau_union_le_sum` to combine

**Advantage**: All lemmas already proven!

### Option B: Prove bridge absorption
1. Prove `bridge_absorbed_by_S_e`
2. Use S_e decomposition with absorption

**Advantage**: Cleaner conceptually, matches Parker's framework.

---

## Next Submission

Create a Lean file that:
1. Uses ONLY proven lemmas (no sorry)
2. Assembles the τ ≤ 8 bound for cycle_4 using per-vertex approach
3. References: slot71 (S_e_structure, tau_union_le_sum) + slot73 (local_cover_le_2, cycle4_all_triangles_contain_shared)

This should be a COMPLETION submission, not an exploration.
