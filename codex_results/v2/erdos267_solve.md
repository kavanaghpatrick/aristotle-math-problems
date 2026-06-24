Added [scripts/erdos267_fibonacci.py](/Users/patrickkavanagh/math/scripts/erdos267_fibonacci.py#L1). It computes exact partial sums `s_t = Σ_{k≤t} 1/F_{n_k}`, a rigorous omitted-tail bound using the next index `n_{t+1}`, and heuristic continued fractions/convergents for the resulting high-precision value. The core analysis/reporting is in [scripts/erdos267_fibonacci.py](/Users/patrickkavanagh/math/scripts/erdos267_fibonacci.py#L178), and the built-in lacunary families are in [scripts/erdos267_fibonacci.py](/Users/patrickkavanagh/math/scripts/erdos267_fibonacci.py#L141).

Key numerics from `python3 scripts/erdos267_fibonacci.py`:
- `pow2`: `log10(q_t * tail)` is `-3.07, -13.10, -53.22` at `t=4,6,8`. Exact partial sums are already far too accurate to converge to a rational. This matches the known special-case behavior.
- `pow3`: even stronger, `-33.88, -304.73, -2742.36`.
- `double_plus_one` (`1,3,7,15,...`): still negative, `-2.25, -4.48, -8.69`, so the simple rational-approximation route still looks viable there.
- `ceil_1p6`: starts negative then turns positive, `-0.28, 2.25, 7.97`. Here the crude denominator argument fails quickly.
- `ceil_1p95`: negative through `t=8`, but with `--terms 10` it becomes positive (`3.67`). So near ratio `2`, exact partial sums alone are not uniformly strong enough.

Proof-direction takeaway:
- Write `A(z) = Σ z^{n_k}`. Using `1/F_n = √5 * Σ_{m≥0} (-1)^{mn} φ^{-(2m+1)n}`, you get
  `S = √5 * Σ_{m≥0} A(((-1)^m φ^{-(2m+1)}))`.
- For `n_k = 2^k`, `A` satisfies a Mahler relation (`A(z) = z^2 + A(z^2)` if you start at `2`), so Mahler-type methods are natural. That explains why the power-of-two case is special.
- For general lacunary `n_k`, there is no comparable functional equation. The more plausible route is gap-series arithmetic: combine lacunarity of `A(z)` with special-value results for algebraic `z` inside the unit disk.
- Continued fractions are useful numerically, but the CF output here does not suggest a universal proof pattern. It mostly reflects that some sums are very close to simple constants after a few dominant terms.
- If you want a uniform irrationality strategy for all `c>1`, the hard regime is the near-threshold one where `q_t * tail_t` stops shrinking. That is where a Mahler-style identity is missing and some sharper structure beyond raw truncations is needed.

Verified by running:
- `python3 scripts/erdos267_fibonacci.py`
- `python3 scripts/erdos267_fibonacci.py --sequence floor_pi --terms 7`
- `python3 scripts/erdos267_fibonacci.py --sequence ceil_1p95 --terms 10`

## Next Steps
1. Run `python3 scripts/erdos267_fibonacci.py --sequence ceil_1p95 --terms 12` to probe the borderline regime further.
2. Add a search mode that scans recurrence-generated lacunary sequences and records where `log10(q_t * tail)` changes sign.
3. If you want a proof sketch next, I’d split it into two tracks: `Mahler for exact self-similar sequences` and `gap-series/Diophantine for general lacunary sequences`.