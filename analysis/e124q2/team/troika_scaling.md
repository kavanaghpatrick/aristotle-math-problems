# troika: Scaling structure & threshold growth for (3,4,7) — reverse-engineering BEGL96

## The exact scaling identity (verified)
For all d, k:  `sumsOfDistinctPowers(d,k) = d^k · S_d`, where `S_d := sumsOfDistinctPowers(d,0)` =
{0-1-digit numbers in base d}. Hence the level-k sumset for D={3,4,7} is
```
R_k = 3^k·S_3 + 4^k·S_4 + 7^k·S_7.
```
Equivalent recursion (verified by exact set equality for k=1,2):
```
R_k = 3·sDP(3,k-1) + 4·sDP(4,k-1) + 7·sDP(7,k-1).
```
The multipliers 3,4,7 are COUPLED — you cannot divide the equation by a single d^k. **This refutes
the naive "subtract a base-7 term, divide by 7^k, reduce to k=0" reduction** (which Grok proposed):
after subtracting 7^k c, the remainder 3^k a + 4^k b is not divisible by 7^k, and dividing by 3^k
leaves the 4^k, 7^k factors. The level-k problem is genuinely coupled, not a clean self-map.

## Monotonicity (verified)
`R_{k+1} ⊆ R_k` for all k (more restrictive ⟹ smaller). So R_k ⊆ R_0, and R_0 is cofinite
(k=0 threshold = 0: EVERY n≥0 representable by {3,4,7} 0-1 sums — this is the Alexeev/Aristotle solve).
The open content: is R_k *also* cofinite for every k≥1, i.e. is the threshold N₀(k) finite?

## Threshold data N₀(k) := largest non-representable integer (all CONVERGED, full coverage above)
| k | N₀(k) | #gaps below N₀ | N₀(k)/84^k |
|---|-------|----------------|------------|
| 0 | 0 | 0 | — |
| 1 | 581 | 37 | 6.92 |
| 2 | 785 743 | 5 205 | 111.4 |
| 3 | 57 751 591 | ~391 000 | 97.4 |

Convergence for k=3 is real: in [58.5M, 117M] there are **0 gaps** (computed via the d^k identity,
N=130M). The gap density is non-monotone (self-similar resurgence in mid-deciles) but terminates.

## Threshold growth law (empirical)
**N₀(k) ≈ C · 84^k** with C ≈ 100 (84 = 3·4·7 = product of bases).
- log_84 N₀(k) = 1.44, 3.06, 4.03 for k=1,2,3 → ≈ k+1 trend.
- This is GEOMETRIC in 84^k, NOT a tower/iterated-exp. **The difficulty is controlled**: a uniform
  -in-k argument at the scale of the base-product 84 should be feasible. The self-similar structure
  R_k = 3·sDP(3,k-1)+4·sDP(4,k-1)+7·sDP(7,k-1) is the engine; the threshold inflates by ~84 per level.

## Why {3,4} alone fails (role of base 7)
{3,4} has density 1/2+1/3 = 5/6 < 1. Its k=0 sumset misses a positive-density, self-similar set of
gaps (62,63, 207–242, 463–482, …) — gap clusters that recur and whose density does NOT vanish.
Base 7 (contributing exactly 1/6, making ∑=1) plugs every gap. The tightness ∑1/(d-1)=1 means base-7
0-1 numbers must hit EVERY {3,4}-gap residue — no slack. This is the combinatorial heart of (3,4,7).

## Status / open
- gcd necessity: DONE (troika_gcd_necessity.md).
- Sufficiency for (3,4,7), all k: the 84^k-controlled self-similar covering is the right frame.
  A rigorous uniform-in-k proof requires showing the gap set of R_k, which lives at scale 84^k,
  is finite — i.e. the covering automaton (process base-3,4,7 digits jointly, low-to-high) reaches
  an all-accepting state after finitely many digit-levels above the forced-zero band of width k.
- General admissible D: every tested family has FINITE k=1 threshold (so (3,4,7) is not special at
  k=1 — see troika_families.md). The tight ∑=1 case is the hardest; ∑>1 cases have slack.
