# Summary of changes for run 1ad22791-3cc4-46c5-a808-36aa5c0fa0bf
## Completed: Sorry-free proof of `powerful_3AP_prime_once_not_dvd`

### File: `RequestProject/Powerful3AP.lean`

The file contains:

1. **Definition `Nat.Powerful`**: A natural number `n` is powerful if every prime dividing it does so with multiplicity ≥ 2 (i.e., `∀ p, p.Prime → p ∣ n → p^2 ∣ n`).

2. **Theorem `powerful_3AP_prime_once_not_dvd`** (sorry-free, axiom-clean — depends only on `propext`):

```
theorem powerful_3AP_prime_once_not_dvd
    (n d p : ℕ) (_hd : 0 < d) (hp : p.Prime)
    (hpd : p ∣ d) (hpp : ¬ p^2 ∣ d)
    (h0 : Nat.Powerful n) (h1 : Nat.Powerful (n + d))
    (_h2 : Nat.Powerful (n + 2 * d)) :
    ¬ p ∣ n
```

### Proof idea

By contrapositive: assume `p ∣ n`. Since `n` is powerful, `p² ∣ n`. Since `p ∣ n` and `p ∣ d`, we get `p ∣ (n+d)`, and since `n+d` is powerful, `p² ∣ (n+d)`. Subtracting `p² ∣ n` from `p² ∣ (n+d)` gives `p² ∣ d`, contradicting the hypothesis `¬ p² ∣ d`.

The formal proof is a clean 3-line tactic proof using `contrapose!`, `Nat.dvd_sub`, and `ring`.

### Scope note

This is a **structural constraint** on the common difference `d` of powerful 3-APs, not a growth-rate lower bound. The abc-conditional lower bound `d ≫ N^{1/2-ε}` (Chan 2022, arXiv:2210.00281) genuinely requires the abc conjecture and cannot be derived from this lemma alone.