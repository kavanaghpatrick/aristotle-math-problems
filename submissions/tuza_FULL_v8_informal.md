# Tuza's Conjecture: τ(G) ≤ 2ν(G)

## The Problem

- **ν(G)** = maximum number of edge-disjoint triangles
- **τ(G)** = minimum edges to delete to make triangle-free
- **Conjecture**: τ(G) ≤ 2ν(G)

Open since 1981. Best known: τ ≤ 1.98ν.

## Available Building Blocks

These lemmas are proven and available:

1. **Base case**: ν = 0 implies τ = 0

2. **Deletion bound**: τ(G) ≤ |S| + τ(G \ S) for any edge set S

3. **Max packing exists**: There exists a packing P with |P| = ν

4. **Every triangle shares an edge with max packing**: If P is max, every triangle in G shares at least one edge with some triangle in P

5. **Triangle has 3 edges**: A triangle has exactly 3 edges

6. **Two edges destroy a triangle**: Removing 2 edges from a triangle destroys it

7. **Monotonicity**: ν(G \ S) ≤ ν(G)

## Prove

Using these building blocks (or ignoring them), prove:

τ(G) ≤ 2 * ν(G)
