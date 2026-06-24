# Summary of changes for run fb9fab9a-5802-4380-9b9e-e8a9b9a7b99b
Successfully formalized and proved the Erdős 938 unconditional upper bound in Lean 4 / Mathlib. The file `RequestProject/Main.lean` contains a complete, sorry-free, axiom-clean proof with the following structure:

**Definitions:**
- `Nat.Powerful n`: a natural number is powerful if `n > 0` and every prime factor appears with exponent ≥ 2.

**Helper lemmas (all sorry-free):**
1. `Nat.powerful_sq`: every positive perfect square is powerful.
2. `Nat.powerful_infinite`: the set of powerful numbers is infinite.
3. `Nat.no_powerful_between_consecutive`: no powerful number lies strictly between two consecutively enumerated powerful numbers (a consequence of `Nat.nth` properties).
4. `Nat.interval_contains_square`: any interval of length > 2√a + 1 starting at `a` contains a positive perfect square.

**Main theorem:**
```lean
theorem erdos_938_unconditional_upper_bound (k : ℕ) :
    let n0 := Nat.nth Nat.Powerful k
    let n1 := Nat.nth Nat.Powerful (k + 1)
    let n2 := Nat.nth Nat.Powerful (k + 2)
    n1 - n0 = n2 - n1 →
    ((n1 - n0 : ℝ) < 2 * Real.sqrt n0 + 2)
```

**Proof idea:** Case-split on whether the "interloper square" `(√n₀ + 1)²` falls below `n₂`. In the positive case, since this square is powerful, it must equal `n₁` (by the no-gap property), giving `d ≤ 2√n₀ + 1`. In the negative case, `n₂ ≤ (√n₀ + 1)²` gives `2d ≤ 2√n₀ + 1`, so `d ≤ √n₀`. Both cases yield `d < 2√n₀ + 2`.

**Axiom check:** Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no custom axioms, no abc-conjecture hypothesis.