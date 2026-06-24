# Techniques — odd multiperfect σ₀ uniform family

## Technique stack (uniform cyclotomic p-adic barrier)

1. **Single-prime collapse** (parameter q). For q prime, σ₀(n) = q ⟹ ∏_{p | n} (a_p + 1) = q ⟹ exactly one prime factor with multiplicity q − 1, hence n = p^(q-1). Mathlib: `Nat.card_divisors`, `Nat.prime_def_lt`. Parameter: q ranges over {11, 13, 17, 19}.

2. **Cyclotomic-polynomial identification**. σ(p^(q-1)) = (p^q − 1)/(p − 1) = Φ_q(p) when q is prime. Mathlib: `Nat.divisors_prime_pow`, `Polynomial.cyclotomic_eq_geom_series` for primes. Parameter-independent identity.

3. **Uniform p-adic-unit barrier**. Φ_q(p) ≡ 1 (mod p) for ANY q ≥ 1, since Φ_q(p) = 1 + p + … (constant term 1, every higher term divisible by p). Mathlib: direct `Nat.add_mod`, `Nat.pow_mod`, no cyclotomic machinery needed.

4. **Multiperfect divisibility lift**. n | σ(n) with k ≥ 2. Specialize: p^(q-1) | σ(p^(q-1)) ⟹ p | σ(p^(q-1)) (since q − 1 ≥ 10 ≥ 1). Mathlib: `dvd_trans`, `dvd_pow_self`.

5. **Uniform contradiction**. Combine 3+4: p | Φ_q(p) and Φ_q(p) ≡ 1 (mod p) ⟹ p | 1, contradicting `Nat.Prime.one_lt`. The contradiction structure is uniform in q.

## Why this is qualitatively different from the slot 746 proof

Slot 746 hard-codes q = 11. The uniform family theorem replaces 11 by a parametric q ∈ {11, 13, 17, 19}, but the proof shape is identical because the barrier Φ_q(p) ≡ 1 (mod p) does not depend on q. The "novel" content is recognizing that the slot 746 proof generalizes verbatim, i.e. it is a Mihăilescu-style uniform cyclotomic argument in disguise. This is a sub-claim closure of an INFINITE family question (odd multiperfect with σ₀(n) ∈ all primes), restricted to the four small primes {11, 13, 17, 19}.

## Lean-Mathlib loadout (Aristotle's MCGS should find these)

- `Nat.card_divisors` (already used by slot 746)
- `Nat.divisors_prime_pow`
- `Nat.add_mod`, `Nat.pow_mod`
- `Polynomial.cyclotomic_prime`, `Polynomial.eval_geom_series` (optional; the proof works without cyclotomic machinery)
- `Nat.Prime.one_lt`
- `Finset.sum_range_succ'`

## Sub-claim closure (CS = sub_claim_closure)

The full infinite uniform family "for ALL odd primes q" requires showing existence (not just non-existence) is excluded, which slot 746's argument also gives. But we restrict to {11, 13, 17, 19} because:
- 11, 13, 17, 19 are the smallest four primes ≥ 11 where the slot 746 argument applies as-is.
- Smaller primes (q ∈ {3, 5, 7}) require additional case-analysis for σ(p^2) parity etc. (e.g. q = 3 case requires Euler's odd-perfect form).
- This is honestly a finite sub-claim, not full closure of "no odd k-multiperfect with σ₀(n) prime", which remains open.

## CR (closure risk) classification

CR = clean_decidable. The four cases dispatch verbatim by the same template. No iff_rfl_trap, no em_tautology (pure ∀-impossibility), no witness_search_explosion (the proof is uniform).
