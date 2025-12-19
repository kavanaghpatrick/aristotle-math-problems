# Complete Tuza's Conjecture for ν ≤ 3

## Context
I have attached a Lean file with PROVEN lemmas from Parker's proof of Tuza for ν ≤ 3.

## What's Already Proven

1. **lemma_2_2**: For any e in max packing M, triangles in S_e pairwise share an edge
2. **lemma_2_3**: ν(G \ T_e) = ν - 1
3. **inductive_bound**: τ(G) ≤ τ(T_e) + τ(G \ T_e)
4. **intersecting_family_structure_corrected**: An intersecting family of triangles is either a STAR or contained in K₄

## What's Needed to Complete

### Step 1: τ(star) ≤ 1
If S is a star (all triangles share a common edge e), then covering e covers all triangles in S.

### Step 2: τ(K₄) ≤ 2
If all triangles are contained in 4 vertices, we can cover them with 2 edges.
(This was proven in a separate run as covering_number_le_two_of_subset_four)

### Step 3: τ(S_e) ≤ 2
Combine: S_e is intersecting (lemma_2_2) → S_e is star or K₄ → τ(S_e) ≤ 2

### Step 4: Final Theorem
For ν ≤ 3: τ(G) ≤ 2ν

Proof by induction on ν:
- Base case ν = 0: τ = 0
- Inductive step: Pick e from max packing M
  - τ(G) ≤ τ(T_e) + τ(G \ T_e) by inductive_bound
  - τ(T_e) ≤ τ(S_e) ≤ 2 by Step 3
  - τ(G \ T_e) ≤ 2(ν-1) by induction (using lemma_2_3)
  - Therefore τ(G) ≤ 2 + 2(ν-1) = 2ν

## Goal
Complete the proof: theorem tuza_nu_le_3 : ν(G) ≤ 3 → τ(G) ≤ 2ν(G)
