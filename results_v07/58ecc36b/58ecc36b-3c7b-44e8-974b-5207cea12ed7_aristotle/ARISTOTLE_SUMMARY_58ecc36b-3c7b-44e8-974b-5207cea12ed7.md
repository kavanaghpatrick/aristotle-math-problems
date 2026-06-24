# Summary of changes
## Erdős Problem 364 — No Three Consecutive Powerful Numbers

**Status: OPEN PROBLEM — `sorry` remains on the main theorem**

This is a genuinely open problem in number theory. No unconditional proof is known, and the ABC conjecture would only imply finitely many counterexamples (not their nonexistence).

### What was formalized (`RequestProject/Erdos364.lean`)

1. **Definition**: `IsPowerful m` — every prime divisor of `m` appears with exponent ≥ 2.

2. **Proved**: `not_powerful_of_two_mod_four` — If `m ≡ 2 (mod 4)`, then `m` is not powerful (since 2 divides `m` but 4 does not).

3. **Proved**: `erdos364_easy_cases` — If `n ≢ 3 (mod 4)`, then `n, n+1, n+2` cannot all be powerful. This covers 3 of 4 residue classes:
   - `n ≡ 0 (mod 4)` → `n+2 ≡ 2 (mod 4)`, not powerful
   - `n ≡ 1 (mod 4)` → `n+1 ≡ 2 (mod 4)`, not powerful  
   - `n ≡ 2 (mod 4)` → `n ≡ 2 (mod 4)`, not powerful

4. **Open** (`sorry`): `erdos364` — The full conjecture. The remaining case `n ≡ 3 (mod 4)` is the core difficulty: `n` and `n+2` are both odd (potentially powerful), and `n+1 ≡ 0 (mod 4)` (so the mod-4 argument doesn't apply to any of them).

### Why the remaining case is hard

I investigated extending the modular sieve to additional primes (3, 5, 7, …), checking whether `p | (n+k)` but `p² ∤ (n+k)` for some `k ∈ {0,1,2}`. This eliminates progressively more residue classes (from 3 survivors mod 36, to 7 mod 180, to 33 mod 1260), but the sieve never terminates — for any finite set of primes, some residue classes survive all checks. Pairs of powerful numbers differing by 2 do exist (e.g., 25 and 27), so the constraint on `n` and `n+2` alone is insufficient; the problem requires that `n+1` is *also* powerful, which appears to need methods beyond modular arithmetic.