# Summary of changes for run 0d6a52af-9166-4d09-b6df-fb581143cf14
## BBC Corollary 1.3 (m=5) — Formalization

### File: `RequestProject/BBCCor13.lean`

I formalized BBC Corollary 1.3 at m=5 from Bajpai–Bennett–Chan (2024, arXiv:2302.03113): conditional on the abc conjecture, only finitely many coprime 5-term powerful arithmetic progressions exist.

### What was proved

The main theorem `bbc_cor_1_3_m5_coprime_finite` has the exact target signature and is structured as a clean two-step reduction:

1. **`bbc_thm_1_1_m5_bound`** — BBC Theorem 1.1 at (m,k)=(5,2): under abc, there exists an absolute bound K such that every coprime 5-term powerful AP (N,d) has max(N,d) < K. **(sorry — see below)**

2. **Main theorem** — The target set is a subset of {(N,d) : max(N,d) < K}, which is finite. **(fully proved from step 1)**

### Helper lemmas (all fully proved, no sorry)

- **`radical_sq_le_of_powerful`** — BBC Lemma 2.1: for a powerful number n, rad(n)² ≤ n. Proved by showing every prime factor has exponent ≥ 2 in the factorization.
- **`coprime_triple_of_coprime`** — For coprime (N,d), the triple {N, d, N+d} is pairwise coprime.
- **`finite_of_max_bounded`** — The set of pairs (N,d) with max(N,d) < K is finite.

### The remaining sorry

The single `sorry` is in `bbc_thm_1_1_m5_bound`, which encapsulates the deep number-theoretic content of BBC's argument. The full derivation requires:
1. The n-term generalization of the abc conjecture (Evertse–Schlickewei theorem for S-unit equations)
2. The 5-term binomial identity a₀ − 4a₁ + 6a₂ − 4a₃ + a₄ = 0 reducing to an S-unit equation
3. Combining radical bounds for powerful numbers with the S-unit theorem to derive gcd(N,d) ≥ c·max(N,d)^{2/7−ε}

I verified through detailed mathematical analysis that the standard 3-term abc conjecture cannot be applied directly to simple triples formed from the AP terms to obtain this bound — the radical of such triples grows too fast relative to the largest term. The BBC argument genuinely requires the n-term abc generalization, which is a substantial piece of mathematics beyond what can be formalized from scratch.

### Verification

- The file compiles cleanly with no lint warnings
- `radical_sq_le_of_powerful`, `coprime_triple_of_coprime`, and `finite_of_max_bounded` have clean axioms (propext, Classical.choice, Quot.sound only)
- The main theorem depends on `sorryAx` only through `bbc_thm_1_1_m5_bound`