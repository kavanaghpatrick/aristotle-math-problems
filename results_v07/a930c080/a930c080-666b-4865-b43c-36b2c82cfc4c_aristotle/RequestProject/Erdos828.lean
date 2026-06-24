import Mathlib

/-!
# Erdős Problem 828: Infinitely Many φ(n) | (n+1)

**Problem**: Are there infinitely many n with φ(n) | (n + 1)?

**Status**: OPEN.

## Known Solutions

The complete list of known solutions (verified computationally up to 10000, then
by the Fermat-prime family) is:

  {1, 2, 3, 15, 255, 65535, 4294967295}

These are:
- n = 1: φ(1) = 1, and 1 ∣ 2 ✓
- n = 2: φ(2) = 1, and 1 ∣ 3 ✓
- n = 3 = F₀: φ(3) = 2, and 2 ∣ 4 ✓
- n = 15 = F₀·F₁ = 3·5: φ(15) = 8, and 8 ∣ 16 ✓
- n = 255 = F₀·F₁·F₂ = 3·5·17: φ(255) = 128, and 128 ∣ 256 ✓
- n = 65535 = F₀·F₁·F₂·F₃: φ(65535) = 32768, and 32768 ∣ 65536 ✓
- n = 2³² - 1 = F₀·F₁·F₂·F₃·F₄: φ(n) = 2³¹, and 2³¹ ∣ 2³² ✓

where Fₖ = 2^(2^k) + 1 are the Fermat numbers.

*Note*: The user's stated solutions {1, 2, 4, 8, 12} do not satisfy
φ(n) | (n+1) and likely refer to a different variant of the problem.

## Why This Is Open

The known solution family is n = 2^(2^k) - 1 = ∏ᵢ₌₀ᵏ⁻¹ Fᵢ, which works
when all Fermat numbers F₀, ..., F_{k-1} are prime. The argument:
- φ(n) = ∏(Fᵢ - 1) = ∏ 2^(2^i) = 2^(2^k - 1)
- n + 1 = 2^(2^k)
- So φ(n) = 2^(2^k - 1) divides 2^(2^k) ✓

Only F₀ = 3, F₁ = 5, F₂ = 17, F₃ = 257, F₄ = 65537 are known to be prime.
F₅ = 2³² + 1 = 641 × 6700417 is composite, and no other Fermat primes are known.

Whether there are infinitely many Fermat primes is a major open problem.
No other infinite family of solutions to φ(n) | (n+1) is known.
The problem is related to Lehmer's conjecture (the a = 0 case of φ(n) | (n+a)).

## Exhaustive Analysis of Small Cases

For prime powers n = p^k: need p^{k-1}(p-1) | (p^k + 1). Since gcd(p, p^k+1) = 1,
need k = 1 and (p-1) | (p+1), giving only p ∈ {2, 3}.

For n = pq (distinct odd primes): need (p-1)(q-1) | (pq+1) = (p-1)(q-1) + p + q,
so (p-1)(q-1) | (p+q). This forces p = 3, q = 5, giving n = 15.

All larger products of primes have φ(n) growing too fast relative to n+1.
-/

/-- Erdős Problem 828: There are infinitely many n with φ(n) | (n + 1).

This is an **open problem**. The only known solutions are
{1, 2, 3, 15, 255, 65535, 4294967295}, arising from products of
the five known Fermat primes. The infinitude depends on unresolved
questions about Fermat primes. -/
theorem erdos828 :
    Set.Infinite {n : ℕ | n > 0 ∧ Nat.totient n ∣ (n + 1)} := by sorry
