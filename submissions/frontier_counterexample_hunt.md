# Tuza Counterexample Hunt

## Goal

Either find a graph G with τ(G) > 2ν(G), or prove that no such graph exists in specific natural graph classes.

## Necessary Conditions for Counterexample

Any counterexample must satisfy ALL of:

1. **ν ≥ 4** (Parker 2024 + our formalization proves Tuza for ν ≤ 3)
2. **χ ≥ 5** (Haxell 1993 proved Tuza for χ ≤ 4)
3. **treewidth ≥ 7** (Botler-Sambinelli 2024)
4. **max average degree ≥ 7** (Puleo 2015)
5. **minimum degree > n/2** (minimal counterexample structure)

## Constraints from Our Proven Lemmas

Our lemmas impose additional constraints:

- **τ(S_e) ≤ 2**: For any packing element e, triangles sharing edge only with e can be covered by 2 edges
- **Pairwise sharing → bounded**: If triangles pairwise share edges, they form star or K4 structure
- **Inductive bound**: τ ≤ τ(T_e) + τ(rest) always holds

## Search Strategy

### Approach 1: Cayley Graphs

Cayley graphs of non-abelian groups have high symmetry that might evade our structural lemmas.

**Candidates**:
- Symmetric group S_n for n ≥ 5
- Alternating group A_5
- PSL(2,p) for small primes

**Argument for abelian case**:
For abelian group G with symmetric generating set S:
- Cayley(G, S) has strong structural properties
- Triangles correspond to 3-term arithmetic progressions in S
- This structure is too regular to be a counterexample

### Approach 2: Graph Products

Products can amplify chromatic number:
- G □ H (Cartesian product): χ(G □ H) = max(χ(G), χ(H))
- G × H (tensor product): χ(G × H) ≤ min(χ(G), χ(H))
- G ⊠ H (strong product): χ(G ⊠ H) = χ(G) · χ(H)

If we can find base graphs with controlled ν and high χ, products might amplify bad behavior.

### Approach 3: Algebraic Constructions

- **Paley graphs**: Strongly regular, already checked - all satisfy Tuza
- **Polarity graphs**: High girth variants might have unusual triangle structure
- **Kneser graphs**: High chromatic number, worth checking triangle structure

## Non-Existence Results (Valuable Even If Negative)

Proving "no counterexample exists in class C" is publishable for natural C:

1. **Cayley graphs of abelian groups**: Likely satisfy Tuza due to structure
2. **Vertex-transitive graphs**: Symmetry might force good covers
3. **Strongly regular graphs**: Fixed parameters constrain triangle structure

## Finite Verification

For small n, we can verify computationally:
- n ≤ 10: Exhaustive check feasible
- n ≤ 15: With pruning by necessary conditions

**Claim**: For n ≤ 12, no counterexample exists.

This would establish that any counterexample requires ≥13 vertices.

## Expected Results

Either:
1. Find explicit counterexample G with τ(G) > 2ν(G)
2. Prove non-existence in natural graph classes
3. Computational verification for small n
