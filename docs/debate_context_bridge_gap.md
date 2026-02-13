# Debate Context: Closing the Bridge Coverage Gap in Tuza ν=4

## The Problem

We are proving Tuza's conjecture for ν=4: every graph with triangle packing number 4 has triangle covering number τ ≤ 8.

We have a complete proof EXCEPT for one case: **PATH_4 with base-edge externals on both endpoints**.

## Setup

A maximal 4-packing M = {A, B, C, D} forms a path:
```
A —[v1]— B —[v2]— C —[v3]— D
```
where A = {v1, a1, a2}, B = {v1, v2, b1}, C = {v2, v3, c1}, D = {v3, d1, d2}.

Adjacent elements share exactly 1 vertex. Non-adjacent share ≤ 1 vertex.

## What's Proven

### Per-Element Coverage (PROVEN: slot331, two_edges_cover_X_and_externals)
For each M-element X, there exist 2 edges e₁, e₂ from X such that:
- Every **external** triangle of X (shares edge with X only) is hit by e₁ or e₂
- X itself contains e₁ or e₂

This uses the **universal apex** lemma: all externals of X either share a common vertex in X (the "apex"), or share a common vertex outside X. Either way, 2 spoke edges from that vertex cover everything.

So 4 × 2 = 8 edges cover all M-elements and all externals.

### The No-Base-External Case (PROVEN: slot548)
If either endpoint (say A) has NO base-edge external (no triangle uses {a1,a2} without v1):
- All T_A triangles contain v1
- τ(T_A) ≤ 2 (two spoke edges from v1)
- remaining(G,A) has ν ≤ 3 (can insert A into any packing of remaining)
- Parker's theorem: ν ≤ 3 → τ ≤ 6
- Total: 2 + 6 = 8 ✓

### Bridge Structure (PROVEN: multiple slots)
- Bridges share edges with 2+ M-elements (by definition)
- Every bridge shares a Sym2 edge with each M-element it touches (slot511)
- Bridge spine coverage: spine edges {v1,v2}, {v2,v3} cover bridges between adjacent M-elements (slot523)

## THE GAP

**Bridge triangles** share edges with 2+ M-elements. The 8 edges chosen to cover externals may NOT cover bridges.

### Why This Is Hard
A bridge B between X and Y shares an edge with X and an edge with Y. We choose 2 edges for X (to cover X's externals) and 2 edges for Y (to cover Y's externals). But:
- The edge B shares with X might not be one of the 2 we chose for X
- The edge B shares with Y might not be one of the 2 we chose for Y
- Both could miss simultaneously!

### Falsified Approaches (DO NOT SUGGEST THESE)

1. **"Bridges are automatically covered by external covers"** — FALSE. Counterexample exists.

2. **Apex-based bridge coverage** — FALSIFIED on Fin 11 (slot543). The claim "at least one apex of X,Y lies in bridge B" is FALSE. Both apexes can be away from B, and no 5-packing exists because replacement triangles lack required edges in sparse graphs.

3. **6-packing argument** — FALSIFIED on K4 (slot529-530). Claiming "at most 2 edge-types have externals" fails when externals form a K4.

4. **LP duality** — Too complex for the theorem prover.

5. **Bridge absorption by S covers** — FALSE. 11 different formulations all failed.

6. **Vertex-saturating cover** — FALSE. Covering all vertices doesn't mean all triangles are hit.

7. **Bridge apex lies on bridge** — FALSE (slot543 counterexample on Fin 11).

## What We Actually Need

Either:
**(A)** A way to choose the 2 edges per M-element that ALSO covers bridges (coordinated selection), OR
**(B)** A proof that bridges in PATH_4 are structurally constrained so the 8 external-covering edges must hit them, OR
**(C)** A completely different argument for τ ≤ 8 in the both-endpoints case that doesn't decompose into "cover externals + cover bridges", OR
**(D)** A modified partition of triangles that avoids the bridge problem entirely.

## Specific Constraints for PATH_4 Both-Endpoints Case

- A has a base-edge external: ∃ triangle T_A using {a1,a2} with v1 ∉ T_A
- D has a base-edge external: ∃ triangle T_D using {d1,d2} with v3 ∉ T_D
- This means τ(T_A) = 3 (need base edge {a1,a2} plus one spoke)
- And τ(T_D) = 3
- Naive bound: 3 + 3 + (middle) ≥ 9 > 8

## The Parker Partition Idea (UNTESTED)

Group S_A ∪ S_B (all triangles sharing edges with A or B) and apply Parker's theorem:
- This group has ν ≤ 3 (otherwise insert A and B for a 5+ packing)
- Parker: τ(S_A ∪ S_B) ≤ 6
- Similarly S_C ∪ S_D has ν ≤ 3, so τ(S_C ∪ S_D) ≤ 6
- BUT S_A ∪ S_B and S_C ∪ S_D overlap on bridges between B and C!
- Need: τ(S_A∪S_B) + τ(S_C∪S_D minus already-covered) ≤ 8
- This requires showing some edges serve double duty

## Key Question for the Debate

What mathematical argument can close the gap from τ ≤ 9 to τ ≤ 8 in the PATH_4 both-endpoints case? The argument must:
1. Not assume bridges are automatically covered (falsified)
2. Not assume apex lies in bridge (falsified)
3. Not assume at most 2 edge-types have externals (falsified)
4. Be formalizable in Lean 4 (for Aristotle to verify)
5. Work for arbitrary graphs, not just specific Fin n instances

## Lean Code: Current Best Proven Result

```lean
-- From slot331 (PROVEN by Aristotle, 12 lemmas):

-- For each M-element X, 2 edges cover X + all its externals
lemma two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (∃ u v, u ∈ X ∧ v ∈ X ∧ (e₁ = s(u,v) ∨ e₂ = s(u,v))) ∧
    (∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2))

-- From slot548 (PROVEN, 0 sorry):
-- If either endpoint has no base-edge external, τ ≤ 8
theorem path4_tau_le_8_no_base_external ...

-- The gap: tau_le_8 when BOTH endpoints have base-edge externals
-- Current best: τ ≤ 9 (3 for endpoint A + 6 via Parker for the rest)
```
