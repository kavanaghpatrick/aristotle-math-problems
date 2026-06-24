You can’t honestly close the full statement with an unconditional proof: as of March 13, 2026, Erdős problem #850 is still listed as open, and the strongest note on the standard reference page is only a conditional “no” under a strong form of `ABC` ([erdosproblems.com/850](https://www.erdosproblems.com/850)). I wrote up the rigorous part we can prove in [erdos850_notes.md](/Users/patrickkavanagh/math/docs/erdos850_notes.md#L1): if a `k=3` witness exists, then with `d = y-x` we must have
`rad(x(x+1)(x+2)) | d`,
so `y = x + tM` with `M = rad(x(x+1)(x+2))`. In particular `x ≡ y (mod 6)` and `|x-y| >= 30`.

I also added a reproducible family-analysis mode to [erdos850_search.py](/Users/patrickkavanagh/math/scripts/erdos850_search.py#L248). The key `k=2` obstruction is the classical infinite family
`x = 2^n - 2`, `y = x(x+2)`.
It works for `k=2` because `y+1 = (x+1)^2`, but it cannot extend to `k=3` since `x+2 = 2^n` has radical `2` while
`y+2 = (x+1)^2 + 1 ≡ 2 (mod 8)` and `y+2 > 2`,
so `y+2` has an odd prime factor and therefore `rad(y+2) > 2 = rad(x+2)`.

Verified runs:
- `python3 scripts/erdos850_search.py --k 3 --bound 1000000` -> no witnesses.
- `python3 scripts/erdos850_search.py --k 3 --bound 10000000` -> no witnesses.
- `python3 scripts/erdos850_search.py --k 2 --bound 1000000 --max-witnesses 6 --family-samples 4` -> reproduces the known `k=2` witnesses and prints why the power-of-two family fails at shift `+2`.

Source used for current status and the classical `k=2` family: [Erdős Problem #850](https://www.erdosproblems.com/850).