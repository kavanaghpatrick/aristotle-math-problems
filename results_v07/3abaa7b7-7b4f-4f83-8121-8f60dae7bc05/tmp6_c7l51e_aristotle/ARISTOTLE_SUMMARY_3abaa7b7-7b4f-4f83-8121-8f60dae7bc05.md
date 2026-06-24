# Summary of changes
Successfully proved `agoh_giuga_five_factors`: any composite squarefree number satisfying both the Carmichael (Korselt) and Giuga conditions must have at least 5 prime factors.

**Theorem proved** (in `AgohGiuga.lean`):
```lean
theorem agoh_giuga_five_factors (n : ℕ) (hn : n > 1)
    (hcomp : ¬ Nat.Prime n) (hsqfree : Squarefree n)
    (hkorselt : ∀ p, Nat.Prime p → p ∣ n → (p-1) ∣ (n-1))
    (hgiuga : ∀ p, Nat.Prime p → p ∣ n → p ∣ (n/p - 1)) :
    4 < n.primeFactors.card
```

**Proof structure** — 10 helper lemmas, all fully proved:

1. **`three_cofactors_lt`** — For 3 distinct naturals ≥ 3: sum of pairwise products < triple product (reciprocal bound ∑1/p < 1 for 3 values)

2. **`four_cofactors_lt`** — Same for 4 distinct naturals ≥ 3 (reciprocal bound for 4 values)

3. **`giuga_prime_ge_three`** — All prime factors ≥ 3 (from Korselt: if 2|n then n-1 is odd, but other prime factors force even divisors of n-1)

4. **`giuga_card_ge_three`** — At least 3 prime factors (2-factor case contradicts `no_giuga_two_factors`)

5. **`prime_dvd_cofactor`** — For distinct prime factors p ≠ q of squarefree n: p | (n/q)

6. **`giuga_sum_mod_prime`** — Each prime factor p divides (∑ n/q) - 1

7. **`giuga_n_dvd_sum_sub_one`** — CRT: n divides (∑ n/p) - 1, using `Finset.prod_primes_dvd`

8. **`giuga_sum_lt_card_three`** / **`giuga_sum_lt_card_four`** — The sum ∑ n/p < n when card is 3 or 4

9. **`giuga_sum_ge_two`** — The sum ∑ n/p ≥ 2

**Main argument**: By contradiction, if card ≤ 4 then card ∈ {3,4}. The CRT gives n | (S-1), the reciprocal bound gives S < n, and S ≥ 2. But n | (S-1) with 0 < S-1 < n is impossible since the smallest positive multiple of n is n itself.

The only `sorry` remaining in the file is `no_carmichael_giuga` — the full open Agoh-Giuga conjecture itself, which was already present before this work.