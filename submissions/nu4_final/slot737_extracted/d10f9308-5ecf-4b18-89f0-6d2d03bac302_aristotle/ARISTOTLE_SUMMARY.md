# Summary of changes for run d10f9308-5ecf-4b18-89f0-6d2d03bac302
## Erdős 647 — Sophie Germain Residue Subclass: PROVED ✓

The theorem `erdos_647_sophie_subclass` has been fully formalized and proved in `RequestProject/Erdos647.lean`, with no `sorry` remaining and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Proof Strategy

The proof proceeds by case analysis on the `hsplit` disjunction, after establishing that 12 ∣ n (from 6 ∣ n and the parity constraint imposed by the primality of q = (n-2)/2).

**Case 1: (2q−1)/3 is not prime** — The witness is m = n−3 = 3·((2q−1)/3). Since (2q−1)/3 ≥ 999 and is composite, we show σ₀(3c) ≥ 6 for any composite c ≥ 999 (using multiplicativity of the divisor function). This gives m + σ₀(m) ≥ (n−3) + 6 = n+3 > n+2.

**Case 2: (q−1)/2 is not prime** — The witness is m = n−4 = 4·((q−1)/2). Since (q−1)/2 ≥ 749 and is composite, we show σ₀(4d) ≥ 7 for any composite d ≥ 749 (again using multiplicativity). This gives m + σ₀(m) ≥ (n−4) + 7 = n+3 > n+2.

### Key Helper Lemmas

- `sigma0_three_mul_composite_ge6`: For composite c ≥ 999, σ₀(3c) ≥ 6
- `sigma0_four_mul_composite_ge7`: For composite d ≥ 749, σ₀(4d) ≥ 7  
- `Nat.card_divisors_composite`: Composite numbers have ≥ 3 divisors
- Several arithmetic identities connecting the hsplit conditions to n−3 and n−4

Both divisor-count lemmas use the multiplicativity of σ₀, decomposing the argument into its prime-power and coprime parts.

Note: The hypothesis `hp1 : Nat.Prime (n-1)` is present in the statement (as part of the Erdős 647 context) but is not needed for this particular subclass proof — the linter warning about it is expected.