# Erdős 203 — Quotient Lift Analysis (May 30 2026)

## TL;DR

**Slot740's 8×8 cover does NOT lift to an infinite Erdős 203 witness.**

The 22-prime greedy cover that catches every cell of `[0,8)²` (at the explicit
m = 1579554969991861182625270235031094424159694) is a **finite-grid artifact**.
Their periodic shadows tile only ~70% of the natural `K×L` quotient; ~30% of
`(k, l)` pairs escape all 22 primes. Concretely, the 8×8 cover does not extend
even to 10×10 (14/100 cells missing).

## Method

1. Enumerated the 69 index-1 primes `3 < p ≤ 500`.
2. For each `p`, computed `m mod p` and the cells `(k,l) ∈ [0,8)²` with
   `2^k · 3^l · m ≡ -1 (mod p)`. 37 primes catch ≥1 cell (a 22-prime greedy subset
   suffices, per Aristotle's set cover); the remaining 14 catch nothing.
3. For each of those 37 cover primes, computed `ord_p(2)`, `ord_p(3)`, and the
   FULL shadow on the quotient `(Z/ord_p(2)) × (Z/ord_p(3))` of (k,l) residues
   killing `2^k · 3^l · m + 1`.
4. Computed the macroscopic quotient periods
   `K = lcm_p ord_p(2)`, `L = lcm_p ord_p(3)`.
5. Tested cover by Monte Carlo (K×L is 50-digit, not directly enumerable).

## The 37 cover primes

| | | | | | | |
|--|--|--|--|--|--|--|
| 5 | 7 | 11 | 13 | 17 | 19 | 29 |
| 31 | 37 | 43 | 53 | 79 | 83 | 89 |
| 101 | 103 | 107 | 109 | 113 | 127 | 131 |
| 137 | 149 | 157 | 173 | 179 | 181 | 211 |
| 227 | 233 | 257 | 293 | 331 | 379 | 389 |
| 449 | 463 | | | | | |

(Aristotle's greedy 22-prime subset is contained in these 37; CRT realization
gives a value of `m` that gets caught by ~15 additional primes "for free.")

## Quotient dimensions

- `K = lcm(ord_p(2)) = 2 624 385 915 867 026 944 432 800` (25 digits)
- `L = lcm(ord_p(3)) = 20 995 087 326 936 215 555 462 400` (26 digits)
- `K × L ≈ 5.5 × 10⁴⁹` — too large to enumerate directly.

## Cover bounds

| Method | Cover fraction |
|--|--|
| Sum of shadow densities (Union bound, UPPER) | **1.0283** |
| Monte Carlo, 200 000 samples on K×L | **0.6936** |
| Empirical 64×64 grid | 0.6982 |
| Empirical 32×32 grid | 0.7070 |
| Empirical 16×16 grid | 0.7461 |
| Empirical 12×12 grid | 0.7986 |
| Empirical 10×10 grid | 0.8600 |
| Empirical 8×8 grid | **1.0000** (slot740's verified cover) |

The 8×8 cover is sharp: cell counts above 8×8 immediately drop coverage below 1.
**No lift.** The structure that makes 8×8 work is finite combinatorial accident
(CRT can hit any finite pattern; covering only fails to lift when shadow density
sum is too small to overcome inevitable overlaps).

## Stress test for slot740's specific m with larger prime bounds

| Bound on p | Index-1 primes | 12×12 covered | 16×16 covered |
|--|--|--|--|
| 500 | 69 | 120/144 | 200/256 |
| 1 000 | 123 | 121/144 | 202/256 |
| 1 500 | 174 | 121/144 | 202/256 |
| 2 000 | 222 | 121/144 | 202/256 |

For Aristotle's specific m, **no new index-1 prime ≤ 2000 catches the 23 missing
12×12 cells**. These cells are systematically uncovered.

## Verdict and branch

**NO_LIFT — slot740 is a finite-grid artifact.**

Therefore: the gap-targeting hedge is the **12×12 generalization** — does ANY
value of m exist for which index-1 primes ≤ 500 cover the 12×12 grid? This is
a sharper bounded-impossibility / existence question. Aristotle can probe it
the same way it did 8×8: greedy CRT-realized set cover, attacking 144 cells.

If 12×12 also covers, slot740's structural failure to lift is not universal —
we need to push K, L instead. If 12×12 cannot be covered (the more likely
outcome given the density numbers above), we have a clean sharper impossibility:
"index-1 primes ≤ 500 are insufficient to cover 12×12."

## Files

- Script: `scripts/erdos203_quotient_lift.py`
- JSON output: `analysis/erdos203_quotient_lift_may30.json`
- Slot740 proof: `submissions/nu4_final/slot740_extracted/.../Main.lean`
- Sketch (drafted, not submitted): `submissions/sketches/erdos203_grid_12x12_B1000.txt`
