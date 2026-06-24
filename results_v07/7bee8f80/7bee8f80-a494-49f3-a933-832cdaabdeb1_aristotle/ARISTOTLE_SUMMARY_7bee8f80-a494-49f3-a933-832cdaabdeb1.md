# Summary of changes
## Erdős Problem 936 — Formalization

**File:** `RequestProject/Erdos936.lean`

### What was done

I formalized the statement of Erdős Problem 936 in Lean 4 with Mathlib:

1. **Defined `Nat.Powerful`**: A natural number is *powerful* (squarefull) if every prime factor appears with exponent ≥ 2. This definition was not in Mathlib, so I wrote it from scratch:
   ```
   def Powerful (n : ℕ) : Prop :=
     ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n
   ```

2. **Stated the theorem** using Lean's `Filter.Eventually` / `Filter.atTop`:
   ```
   theorem erdos_936 :
       ∀ᶠ n in atTop, ¬ (2 ^ n + 1 : ℕ).Powerful := by sorry
   ```

### Why the proof remains `sorry`

This is a **genuinely open problem** in number theory. No unconditional proof is known. The result does follow from the ABC conjecture (also unproven): if 2^n + 1 were powerful, its radical would be at most (2^n+1)^{1/2}, contradicting the ABC bound for the equation 1 + 2^n = (2^n + 1).

I attempted multiple proof strategies with the theorem-proving subagent, including:
- Covering system approaches using small primes (3, 5, 17, 257) to show specific residue classes yield non-powerful values
- Zsygmondy's theorem to find primitive prime divisors

These partial approaches can handle many residue classes (e.g., n ≡ 1 or 5 mod 6 via the prime 3, and n ≡ 2, 6, 14, 18 mod 20 via the prime 5) but cannot cover all residue classes with finitely many primes — which is precisely why the problem remains open.

The file compiles cleanly and includes documentation explaining the problem's status and the ABC conjecture connection.