I added a search script at [analysis/erdos273_cover_search.py](/Users/patrickkavanagh/math/analysis/erdos273_cover_search.py#L1) and a short writeup at [analysis/ERDOS273_NOTES.md](/Users/patrickkavanagh/math/analysis/ERDOS273_NOTES.md#L1). I also verified the problem is still listed as open on Erdős Problems, last edited October 1, 2025: https://www.erdosproblems.com/273.

The key reduction is the useful part: since every allowed modulus is even, any solution would split by parity into two disjoint distinct covering systems after halving the moduli. So Problem 273 is equivalent to finding two disjoint covers with moduli `n` such that `2n+1` is prime; that also explains why the `p >= 3` case is easier, because modulus `2` becomes the trivial half-modulus `1`. The note records the necessary density constraints: each parity side must have reciprocal mass at least `1`, so in the original variables each parity bucket must contribute at least `1/2`, hence total `sum 1/m >= 1`. It also records the standard prime-power divisibility screen used by the script.

The script compiled cleanly and I ran it on two bounded families. For divisors of `2520`, the half-side reciprocal mass is only `1.903571`, so two disjoint half-covers are impossible there by density alone. For divisors of `27720`, the half-side mass is `2.087338`, and the script found an exact single half-cover:
`0 mod 2, 0 mod 3, 0 mod 5, 1 mod 6, 3 mod 8, 2 mod 9, 2 mod 15, 5 mod 18, 3 mod 20, 11 mod 30, 17 mod 36, 89 mod 90`.
A one-trial disjoint-pair attempt did not find a second side; the best second-side uncovered fraction was `0.622475`, so the easy greedy search is still far from a full construction.

Verification: `python3 -m py_compile analysis/erdos273_cover_search.py` passed. Useful commands are:
```bash
python3 analysis/erdos273_cover_search.py --mode report
python3 analysis/erdos273_cover_search.py --period '2^3*3^2*5*7*11' --mode single --trials 20
python3 analysis/erdos273_cover_search.py --period '2^3*3^2*5*7*11' --mode pair --trials 1
```