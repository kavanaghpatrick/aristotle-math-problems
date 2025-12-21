# Tuza Conjecture: τ(T_e) ≤ 2 for ν ≤ 3

## What We Have Proven (from 4736da84)

1. **S_e_pairwise_share_edges**: All triangles in S_e pairwise share an edge
2. **tau_S_le_2**: τ(S_e) ≤ 2 for any e ∈ M (max packing)
3. **Te_eq_Se_when_nu_1**: When ν = 1, T_e = S_e
4. **tuza_nu_le_3** (conditional): The main theorem, assuming tau_Te_le_2_of_nu_le_3

## Target Lemma

**Lemma (tau_Te_le_2_of_nu_le_3)**: For any graph G with ν(G) ≤ 3, and any e in a maximum triangle packing M, we have τ(T_e) ≤ 2.

## Definitions

- **T_e** = {t ∈ triangles(G) : t shares an edge with e} (triangles sharing ≥2 vertices with e)
- **S_e** = {t ∈ T_e : t shares an edge ONLY with e, not with any other f ∈ M}
- **T_e \ S_e** = triangles that share edges with both e AND some other f ∈ M

## Proof Strategy

**Case ν = 1**: T_e = S_e (proven), so τ(T_e) = τ(S_e) ≤ 2.

**Case ν = 2**: M = {e, f} for some f ≠ e.
- T_e = S_e ∪ (T_e ∩ T_f)
- Triangles in T_e ∩ T_f share edges with BOTH e and f
- Since e, f are edge-disjoint (in packing), these triangles have ≥4 vertices
- Any triangle sharing edges with both e and f must contain the edge e ∩ f... but wait, e and f are edge-disjoint so (e ∩ f).card ≤ 1
- So triangles in T_e ∩ T_f share different edges with e and f
- Key: The edge of t shared with e is covered by the same covering that covers S_e

**Case ν = 3**: M = {e, f, g}.
- T_e = S_e ∪ (triangles also sharing with f) ∪ (triangles also sharing with g)
- Same argument: edges covering S_e also cover the "overlap" triangles

## Key Insight

The covering edges for S_e are edges OF the triangles in S_e. Any triangle t in T_e shares an edge with e. If t ∉ S_e, then t also shares an edge with some f ≠ e in M.

But the edge t shares with e is still an edge of t! So if we pick the covering edges from within the triangles (which we do for S_e), those same edges work for all of T_e.

More precisely: Let C be a minimum cover for S_e with |C| ≤ 2. For any t ∈ T_e:
- If t ∈ S_e, then t is covered by C (by definition)
- If t ∈ T_e \ S_e, then t shares edge e' with e where e' ⊆ t ∩ e
- Since t shares an edge with e, and S_e contains ALL triangles sharing the edge e' with e that don't share with other packing elements...
- Actually this needs more care: the edge might be different

## Alternative: Use Parker's approach

Parker (2025) proves τ(T_e) ≤ 2 by showing:
1. Pick e ∈ M minimizing τ(S_e)
2. Show T_e \ S_e triangles are "absorbed" by the S_e covering

The key is that when ν ≤ 3, for each triangle t in T_e \ S_e, the edge t shares with e is one of at most 3 possible edges of e. With only 2 other packing elements (f, g), the structure is constrained enough that 2 edges suffice.

## Theorem Statement (Lean)

```lean
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2
```
