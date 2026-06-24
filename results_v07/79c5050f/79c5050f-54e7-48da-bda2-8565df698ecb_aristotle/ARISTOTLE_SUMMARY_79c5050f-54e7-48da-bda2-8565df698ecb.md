# Summary of changes
## Erdős Problem 672 (k = 35) — Formalization

**File:** `RequestProject/Erdos672.lean`

### What was done

I formalized the statement of Erdős Problem 672 for k = 35:

```lean
theorem erdos_672_k35 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ∀ l : ℕ, l ≥ 2 →
    ¬ ∃ y : ℕ, (∏ i ∈ Finset.range 35, (n + i * d)) = y ^ l
```

The statement compiles correctly against Mathlib.

### Status: OPEN — Proof not found

This is a **genuinely open problem** in number theory. The theorem proving subagent was unable to find a proof, which is consistent with the mathematical status:

- **Solved cases:** k ≤ 34 (Bennett–Bruin–Győry–Hajdu 2006; Győry–Hajdu–Pintér 2009) and k sufficiently large (Bennett–Siksek 2020).
- **Open gap:** 35 ≤ k ≤ threshold, with k = 35 being the first unsolved case.

The known approaches for smaller k involve reducing to systems of Thue–Mahler equations and hyperelliptic curves, but the combinatorial explosion at k = 35 has prevented resolution. The file includes detailed documentation of the mathematical background and known results.

The theorem remains as `sorry`.