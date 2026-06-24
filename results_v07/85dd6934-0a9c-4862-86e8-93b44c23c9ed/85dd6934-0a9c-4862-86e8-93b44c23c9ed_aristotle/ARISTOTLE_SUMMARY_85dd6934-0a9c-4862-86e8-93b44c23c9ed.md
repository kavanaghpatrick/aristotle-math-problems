# Summary of changes
## Kurepa's Conjecture — Open Problem

The file `RequestProject/Kurepa.lean` contains the formal statement of Kurepa's Conjecture:

```lean
theorem kurepa (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ¬ p ∣ (∑ i ∈ Finset.range p, i.factorial) := by sorry
```

**This remains `sorry`'d because Kurepa's Conjecture is a genuine open problem in number theory**, unsolved since 1971.

### What was attempted

1. **Verified the conjecture computationally** for all odd primes up to 47, confirming `!p mod p ≠ 0` in each case.

2. **Investigated the Barsky–Benzaghou claim** from the problem statement. The suggested formula would imply `!p ≡ 1 (mod p)`, but this is **false**: `!5 = 34 ≡ 4 (mod 5)`, `!7 = 874 ≡ 6 (mod 7)`. The residues `!p mod p` vary with no discernible pattern, so this approach does not resolve the conjecture.

3. **Multiple automated proof attempts** were made using algebraic manipulation in `ZMod p`, Wilson's theorem, polynomial generating functions, and recurrence-based arguments. None succeeded, consistent with the problem's open status.

### Mathematical context (documented in the file)

- Verified computationally for primes up to 2^34 (Andrejić–Tatarevic, 2015)
- Equivalent to `gcd(!p, p!) = 2` for odd primes (Kurepa)
- Connected to derangement numbers and Wilson's theorem
- No known proof or disproof exists as of 2024