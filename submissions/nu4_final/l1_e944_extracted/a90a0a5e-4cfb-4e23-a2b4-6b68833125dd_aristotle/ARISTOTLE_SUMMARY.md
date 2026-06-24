# Summary of changes for run a90a0a5e-4cfb-4e23-a2b4-6b68833125dd
## Erdős Problem 944 — Dirac's Conjecture, k = 4 case

### What was done

I formalized the k=4 case of Dirac's 1970 conjecture in `RequestProject/Main.lean`. The file contains:

1. **`SimpleGraph.IsVertexCritical`**: A graph G is k-vertex-critical if χ(G) = k and for every vertex v, the induced subgraph on V \ {v} has chromatic number strictly less than k.

2. **`SimpleGraph.IsEdgeCritical`**: An edge e of G is critical if removing it strictly drops the chromatic number.

3. **`erdos_944_k_eq_four`**: The main theorem statement — there exists a finite 4-vertex-critical graph in which no single edge is critical.

The file builds cleanly against Mathlib (Lean 4.28.0).

### Why the `sorry` remains

This is a **genuinely open problem** — the last remaining case of Dirac's 1970 conjecture. The status:

- **k ≥ 5**: Resolved positively (Brown 1992 for k=5, Jensen 2002 for all k ≥ 5).
- **k = 4**: **Open.** No known construction works:
  - Brown's k=5 example does not descend to k=4.
  - Jensen's family starts at k=5.
  - Lattanzio's "k−1 not prime" condition fails since 3 is prime.

Neither a witness graph nor a proof that none exists has been found in the mathematical literature. The automated proof search was also unable to resolve this, as expected for an open problem. The `sorry` accurately reflects the current state of mathematical knowledge.