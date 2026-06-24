# Summary of changes
## Erdős Problem 828: φ(n) ∣ (n + a) infinitely often

**File**: `RequestProject/Erdos828.lean`

### Status: OPEN — main theorem left with `sorry`

This is a known open problem in number theory (Erdős Problem 828). The main theorem states that for every integer `a`, the set `{n : ℕ | φ(n) ∣ n + a}` is infinite.

### What was accomplished

1. **Proved two special cases** as supporting lemmas:
   - `erdos_828_neg_one` (a = -1): Every prime p satisfies φ(p) = p-1 | p-1, and there are infinitely many primes. ✓
   - `erdos_828_zero` (a = 0): Every n = 2^k satisfies φ(2^k) = 2^(k-1) | 2^k, and there are infinitely many powers of 2. ✓

2. **Main theorem** `erdos_828` remains `sorry`'d — this is expected for an open problem.

### Why the general case is hard

For any fixed "template" n = c·p (c fixed, p prime), the divisibility condition φ(c)(p-1) | cp + a reduces to φ(c)(p-1) | (c + a), yielding only finitely many primes p. Using products of multiple primes (n = c·p·q) doesn't overcome this because the growth rates of φ(n) and n+a are too close. The general case likely requires sieve-theoretic methods or fundamentally different constructions not currently available in Mathlib. The problem remains open as of 2024.