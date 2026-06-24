# Summary of changes for run 9fa69652-7f15-4ebc-8c5c-16e4dd35f7c3
Successfully proved `erdos_647_cunningham_residual_bounded` in `RequestProject/Main.lean`.

**Theorem statement:** For every n ∈ [3000, 10⁶] with n ≡ 0 (mod 6), n−1 prime, (n−2)/2 prime, ((n−2)/2−1)/2 prime, and (2·(n−2)/2−1)/3 prime (the 35 Cunningham-chain configurations), there exists m < n such that m + σ₀(m) > n + 2.

**Proof strategy:** A two-step approach:

1. **Witness table lemma** (`erdos_647_witness_table`): For all qualifying n in the range, either m = n−5 or m = n−6 satisfies m + σ₀(m) > n + 2. This is verified computationally via `native_decide` over the full range [3000, 10⁶]. The `native_decide` check runs efficiently because the primality conditions filter the ~10⁶ candidates down to exactly 35 values, and only two σ₀ evaluations are needed per qualifying n.

2. **Main theorem**: Case-splits on the disjunction from the witness table and constructs the existential witness as `⟨n−5, _⟩` or `⟨n−6, _⟩ : Fin n`.

The proof uses only standard axioms (propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound) — no sorry, no custom axioms.