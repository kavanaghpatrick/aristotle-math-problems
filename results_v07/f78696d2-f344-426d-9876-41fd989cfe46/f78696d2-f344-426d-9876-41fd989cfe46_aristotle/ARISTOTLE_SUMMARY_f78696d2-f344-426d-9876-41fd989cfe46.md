# Summary of changes
## Lehmer's Totient Problem — Formalization

**Status: OPEN PROBLEM** — The main conjecture `lehmer_totient` remains with `sorry`, as this is a genuinely open problem in number theory (Lehmer, 1932). No proof or counterexample is known.

### What was accomplished

In `RequestProject/LehmerTotient.lean`, I formalized and **fully proved** all the known partial results toward Lehmer's conjecture:

1. **`coprime_pred`** — Consecutive natural numbers are coprime (auxiliary lemma).

2. **`lehmer_squarefree`** — Any counterexample must be squarefree. *Proof:* if p² | n then p | φ(n) | (n−1), but p | n, so p | gcd(n, n−1) = 1, contradiction.

3. **`even_totient_of_even_gt_two`** — For n > 2, φ(n) is even.

4. **`lehmer_odd_or_prime`** — Any number satisfying the Lehmer condition is either odd or prime (i.e., any composite counterexample must be odd). *Proof:* if n is even and n > 2, then φ(n) is even but n−1 is odd, so φ(n) ∤ (n−1).

5. **`prime_sub_one_dvd_totient`** — If p is prime and p | n, then (p−1) | φ(n).

6. **`lehmer_carmichael`** — The Carmichael condition: if φ(n) | (n−1) and p is a prime divisor of n, then (p−1) | (n−1).

### The main conjecture

```lean
theorem lehmer_totient (n : ℕ) (hn : n > 1)
    (hdvd : Nat.totient n ∣ (n - 1)) :
    Nat.Prime n := by sorry
```

This remains `sorry`'d as it is an open problem. The theorem proving subagent was unable to find a proof, which is expected — any composite counterexample must have ≥ 15 prime factors and exceed 10^30, and no mathematical proof closing the gap is known.