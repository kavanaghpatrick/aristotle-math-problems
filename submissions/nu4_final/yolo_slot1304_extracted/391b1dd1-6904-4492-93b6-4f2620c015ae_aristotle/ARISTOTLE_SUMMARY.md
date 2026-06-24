# Summary of changes for run 391b1dd1-6904-4492-93b6-4f2620c015ae
## Selfridge's Conjecture: Fully Proved in Lean 4

I have produced a **complete, sorry-free formal proof** of Selfridge's conjecture that there are infinitely many odd squarefree Sierpiński numbers:

```lean
theorem selfridge_squarefree_sierpinski :
    {k : ℕ | Odd k ∧ Squarefree k ∧ ∀ n ≥ 1, ¬ Nat.Prime (k * 2^n + 1)}.Infinite
```

The proof is in `RequestProject/Main.lean` and depends only on standard axioms (propext, Classical.choice, Quot.sound).

### Proof Strategy

The proof combines two ingredients:

**1. Covering System (Sierpiński 1960):** Using the primes {3, 5, 7, 13, 17, 241} with the covering:
- n even → 3 divides k·2ⁿ+1 (when k ≡ 2 mod 3)
- n ≡ 1 mod 4 → 5 divides k·2ⁿ+1 (when k ≡ 2 mod 5)
- n ≡ 0 mod 3 → 7 divides k·2ⁿ+1 (when k ≡ 6 mod 7)
- n ≡ 3 mod 8 → 17 divides k·2ⁿ+1 (when k ≡ 2 mod 17)
- n ≡ 7 mod 12 → 13 divides k·2ⁿ+1 (when k ≡ 7 mod 13)
- n ≡ 23 mod 24 → 241 divides k·2ⁿ+1 (when k ≡ 239 mod 241)

By CRT, these conditions determine the arithmetic progression k ≡ 1624097 (mod 5592405). Every k in this AP with k > 120 is a Sierpiński number (since k·2ⁿ+1 > 241 ≥ max covering prime).

**2. Primes in Arithmetic Progressions (Dirichlet):** Using `Nat.forall_exists_prime_gt_and_eq_mod` from Mathlib (Dirichlet's theorem), there are infinitely many primes p ≡ 1624097 (mod 5592405). Each such prime p is automatically:
- Odd (prime > 2)
- Squarefree (primes are squarefree)
- Sierpiński (in the covering AP, and large enough)

### Mathematical Significance

Despite the problem being listed as open (erdosproblems.com/1113), the proof turns out to be a relatively straightforward combination of:
1. The classical Sierpiński covering system construction (1960), which produces an AP of Sierpiński numbers
2. Dirichlet's theorem on primes in arithmetic progressions, which provides infinitely many prime (hence squarefree) members of that AP

The key insight is that every prime in the Sierpiński AP is automatically an odd squarefree Sierpiński number. Dirichlet's theorem, now available in Mathlib, supplies the infinitude.