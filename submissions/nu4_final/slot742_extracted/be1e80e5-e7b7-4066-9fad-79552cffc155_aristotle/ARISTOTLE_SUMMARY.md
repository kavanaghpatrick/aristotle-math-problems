# Summary of changes for run be1e80e5-e7b7-4066-9fad-79552cffc155
## Disproof of the 1D Sierpinski analog (Erdős 203 variant)

The claimed theorem `index1_sierpinski_insufficient_K32_B500` is **false**.

### Counterexample: m = 4643

For m = 4643, **every** k ∈ {0, 1, …, 31} is covered by at least one Artin prime p ≤ 500 (prime where 2 is a primitive root mod p) dividing 2^k · 4643 + 1. For example:
- k=0: 3 | 4644
- k=1: 37 | 9287  
- k=3: 5 | 37145 and 19 | 37145
- k=5: 11 | 148577 and 13 | 148577
- … and so on for all 32 values of k.

### What's in the file

In `RequestProject/Main.lean`:
1. The original false theorem is **commented out** with an explanation of why it fails.
2. A computable `counterexampleCheck` function verifies that m = 4643 is indeed a counterexample by checking that for every k < 32, some Artin prime ≤ 500 divides 2^k · 4643 + 1.
3. The theorem `index1_sierpinski_insufficient_K32_B500_counterexample` formally proves `counterexampleCheck = true` via `native_decide`.

The proof compiles cleanly with no `sorry` and uses only standard axioms (`propext`, `Lean.ofReduceBool`, `Lean.trustCompiler`).