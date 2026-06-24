# Summary of changes for run 279e0cb3-6158-4d31-ad2d-4e6cb1be70b4
Successfully proved `erdos_647_residual_bounded_iter2` in `RequestProject/Erdos647.lean`.

**Theorem:** For every integer n with 3000 ≤ n ≤ 10⁶, n ≡ 0 (mod 6), n−1 prime, (n−2)/2 prime, ((n−2)/2−1)/2 prime, and (2·(n−2)/2−1)/3 prime, there exists m < n with n + 2 < m + σ₀(m).

**Proof strategy:** The Sophie-Germain Cunningham-chain conditions filter the ~998,000 candidates in [3000, 10⁶] down to exactly 35 qualifying values of n. For each, either m = n−5 or m = n−6 serves as a witness (the divisor count σ₀(m) is large enough because these values land on highly composite numbers). This is verified by a helper lemma `e647_witness_table` proved via `native_decide`, which compiles in ~17 seconds. The main theorem derives the existential by case-splitting on the witness disjunction and packaging the witness as a `Fin n` element.

**Verification:** The proof compiles cleanly with no `sorry`, and uses only standard axioms (`propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Quot.sound`).