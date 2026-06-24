# Summary of changes
## Euler's Sum of Powers Conjecture (k ≥ 6) — Open Problem

The theorem has been formalized in `RequestProject/EulerPowers.lean` with the statement:

```lean
theorem euler_powers_k6 (k : ℕ) (hk : k ≥ 6) (a : Fin (k-1) → ℕ)
    (ha : ∀ i, a i > 0) (b : ℕ) (hb : b > 0) :
    ∑ i, (a i)^k ≠ b^k := by
  sorry
```

**This is a genuine open problem** and the `sorry` remains. No proof is known as of 2025, and the theorem proving subagent was unable to find one (as expected for an open problem).

The file includes detailed documentation covering:
- The history of the conjecture (Euler 1769, Lander–Parkin 1966, Elkies 1988)
- Known counterexamples for k = 4 and k = 5
- Why natural proof approaches (size arguments, p-adic obstructions, Fermat-style descent) fail to generalize to this setting
- References to the key papers

The file compiles cleanly (modulo the expected `sorry` warning).