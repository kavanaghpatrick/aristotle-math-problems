Added [scripts/erdos366_search.py](/Users/patrickkavanagh/math/scripts/erdos366_search.py). The core search is in [scripts/erdos366_search.py:126](/Users/patrickkavanagh/math/scripts/erdos366_search.py#L126) and [scripts/erdos366_search.py:159](/Users/patrickkavanagh/math/scripts/erdos366_search.py#L159): it enumerates `3`-full numbers `m = n+1`, then exact-tests whether `m-1` is `2`-full. The local residue analysis is in [scripts/erdos366_search.py:98](/Users/patrickkavanagh/math/scripts/erdos366_search.py#L98).

Verified runs:
- `python3 scripts/erdos366_search.py --limit 1000000000000` found no solution up to `10^12` after checking `41,135` `3`-full candidates in `13.263s`.
- `python3 scripts/erdos366_search.py --limit 10000000000000` found no solution up to `10^13` after checking `90,618` `3`-full candidates in `120.882s`.
- `python3 scripts/erdos366_search.py --limit 1000 --local-primes 2,3 --enumerate-local-up-to 1000` confirms there are `39` locally admissible classes mod `216`, so small-modulus local filters do not kill the problem.

Main structural takeaway:
- Pure per-prime local conditions are too weak. For each prime `p`, the number of admissible residues mod `p^3` is
  `p^3 - 2p^2 + p + 1`.
- Hence for any finite prime set `S`, the number of locally admissible classes mod `∏ p^3` is
  `∏(p^3 - 2p^2 + p + 1)`, which is always positive.
- So any proof has to use a genuinely global obstruction, not just “if `p|n` then `p^2|n`, if `p|n+1` then `p^3|n+1`” on finitely many primes.

Two easy local consequences worth keeping in mind:
- Mod `8`, `n` must lie in `{0,4,7}`.
- Mod `27`, if `3` divides one of `n,n+1`, then the divisibility is forced up to `9` on `n` or `27` on `n+1`.

I couldn’t create a git branch here because writes under `.git/refs` are blocked by the sandbox, but the script itself is in place and runnable.