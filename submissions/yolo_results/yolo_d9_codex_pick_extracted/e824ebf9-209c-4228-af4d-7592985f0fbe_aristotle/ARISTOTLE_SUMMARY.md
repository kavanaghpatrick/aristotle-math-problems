# Summary of changes for run e824ebf9-209c-4228-af4d-7592985f0fbe
# Attack on Open Problem: 9 ∣ C(2^(k+1), 2^k) for k ≥ 3, k ∉ {6, 8}

This is a formalization of an **open problem** from Holdum-Klausen-Rasmussen 2026 (arXiv:2601.09510). The conjecture states that 9 divides the central binomial coefficient C(2^(k+1), 2^k) for all k ≥ 3 except k = 6 and k = 8. The unconditional proof remains open — the authors verify it computationally for k ≤ 10^13 and prove the density of exceptional k is zero, but cannot prove it for all k.

## What was accomplished

The file `RequestProject/Main.lean` contains a comprehensive partial proof with a single `sorry` isolating the open content.

### Proof structure

**1. Kummer carry reduction (fully proven):**
Using Mathlib's `padicValNat_choose`, I proved that `v_3(C(2^(k+1), 2^k))` equals the number of "carry positions" i where `3^i ≤ 2·(2^k mod 3^i)`. The key lemma `nine_dvd_central_binom_of_two_carries` shows that if any two such carry positions exist, then 9 divides the binomial coefficient.

**2. Finite verification (fully proven):**
All cases k = 3, 4, 5, 7, 9, 10, ..., 20 verified by `native_decide`.

**3. Infinite families via modular arithmetic (fully proven):**
By analyzing `2^k mod 3^j` for j = 1, 2, 3, 4, I unconditionally proved the result for 34 out of 54 residue classes (≈ 63% of all k):

| Residue class | Carry positions | Why |
|---|---|---|
| k ≡ 3 (mod 6) | i = 1, 2 | 2^k mod 3 = 2, mod 9 = 8 |
| k ≡ 5 (mod 6) | i = 1, 2 | 2^k mod 3 = 2, mod 9 = 5 |
| k ≡ 7 (mod 18) | i = 1, 3 | 2^k mod 3 = 2, mod 27 = 20 |
| k ≡ 4 (mod 18) | i = 2, 3 | 2^k mod 9 = 7, mod 27 = 16 |
| k ≡ 10 (mod 18) | i = 2, 3 | 2^k mod 9 = 7, mod 27 = 25 |
| k ≡ 12, 30, 32, 50 (mod 54) | i = 3, 4 | carry conditions at mod 27 and mod 81 |
| k ≡ 19, 31 (mod 54) | i = 1, 4 | carry conditions at mod 3 and mod 81 |
| k ≡ 52 (mod 54) | i = 2, 4 | carry conditions at mod 9 and mod 81 |

**4. Remaining open gap (sorry):**
The theorem `div9_open` contains the single `sorry`. It covers k > 20 in the 20 remaining residue classes mod 54: {0, 1, 2, 6, 8, 13, 14, 16, 18, 20, 24, 26, 34, 36, 37, 38, 42, 44, 48, 49}. This could be further reduced by analyzing higher powers of 3 (the pattern resolves ≈ 1/3 of remaining cases at each level), but the full unconditional statement requires understanding the global base-3 digit structure of powers of 2 — which is the core open problem.

### Mathematical insight

The problem reduces to showing that 2^k in base 3 always generates at least 2 "carries" when doubled. Each carry at position i corresponds to `2^k mod 3^i ≥ ⌈3^i/2⌉`. The carry structure is periodic mod `2·3^(j-1)` at digit position j, so finite levels of modular arithmetic each resolve some cases, but at every finite level some residue classes escape — this is the fundamental obstruction to an unconditional proof.