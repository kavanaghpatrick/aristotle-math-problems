# Summary of changes for run 15df50b8-6325-4db4-a4d9-026ea0da5ac7
## Erdős 938 — gcd(n_k, d) is powerful: Fully proved

I formalized and proved the theorem `erdos_938_gcd_powerful` in `RequestProject/Erdos938.lean`. The theorem states:

> If the k-th, (k+1)-th, and (k+2)-th powerful numbers form an arithmetic progression with common difference d, then gcd(n_k, d) is powerful.

### Proof structure

1. **Definition**: `Nat.Powerful n` is defined as `0 < n ∧ ∀ p, p.Prime → p ∣ n → p² ∣ n`.

2. **Infinitude**: The set of powerful numbers is infinite (since every perfect square ≥ 1 is powerful).

3. **Key valuation lemma** (`slot_1329`): If n, n+d, n+2d are all powerful and p is prime with p ∣ d but p² ∤ d, then p ∤ n. The proof is a one-line contradiction: if p ∣ n, then p² ∣ n (n is powerful), so p² ∤ (n+d) (by `not_sq_dvd_add`), but p ∣ (n+d) and n+d is powerful forces p² ∣ (n+d) — contradiction.

4. **Main theorem**: For any prime p dividing gcd(n₀, d), we have p ∣ n₀ and p ∣ d. By slot_1329 (contrapositive), p² ∣ d. Since n₀ is powerful, p² ∣ n₀. Hence p² ∣ gcd(n₀, d), making gcd(n₀, d) powerful.

### Verification

- Builds cleanly with no warnings and no `sorry`
- Only standard axioms used: `propext`, `Classical.choice`, `Quot.sound`