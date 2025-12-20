# Tuza's Conjecture - Formalized Proofs

## The Conjecture

**Tuza's Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G), where:
- τ(G) = minimum number of edges needed to hit all triangles (covering number)
- ν(G) = maximum number of edge-disjoint triangles (packing number)

## Proven Cases

| Case | Bound | Status | Proof File |
|------|-------|--------|------------|
| ν = 0 | τ = 0 | **PROVEN** | `nu0/tuza_nu0_PROVEN.lean` |
| ν = 1 | τ ≤ 2 | **PROVEN** | `nu1/tuza_nu1_PROVEN.lean` |
| ν = 2 | τ ≤ 4 | **PROVEN** | `nu2/tuza_nu2_PROVEN.lean` |
| ν = 3 | τ ≤ 6 | Pending | (submissions running) |

## Aristotle UUIDs

- **ν=0, ν=1**: `2b21c426-552d-4eb4-831e-b797545758e2`
- **ν=2**: `0764be78-b5d4-4f03-a32f-dc5efb92806d`
- **Parker lemmas**: `181fa406-e8a7-4f19-925a-f3ae337bc3db`

## Folder Structure

```
proven/tuza/
├── README.md           (this file)
├── nu0/
│   └── tuza_nu0_PROVEN.lean
├── nu1/
│   └── tuza_nu1_PROVEN.lean
├── nu2/
│   └── tuza_nu2_PROVEN.lean
└── lemmas/
    └── parker_lemmas.lean
```

## Key Lemmas (in lemmas/)

From Parker's paper (arXiv:2406.06501):

- `lemma_2_2`: Triangles in S_e pairwise share edges
- `lemma_2_3`: ν(G\T_e) = ν - 1 after removing packing element
- `inductive_bound`: τ(G) ≤ τ(T_e) + τ(G\T_e)
- `tau_S_le_2`: τ(S_e) ≤ 2

## Verification

All proofs compile with Lean 4 / Mathlib:
```bash
lake env lean proven/tuza/nu0/tuza_nu0_PROVEN.lean  # Should show no errors
lake env lean proven/tuza/nu1/tuza_nu1_PROVEN.lean
lake env lean proven/tuza/nu2/tuza_nu2_PROVEN.lean
```

## References

- Tuza, Zs. (1981). Conjecture first stated
- Haxell, P. (1999). Best known bound: τ ≤ (3-ε)ν
- Parker, A. (arXiv:2406.06501, May 2025). Proved τ ≤ 2ν for ν ≤ 3
- These formalizations: Verified by Aristotle theorem prover (Dec 2025)
