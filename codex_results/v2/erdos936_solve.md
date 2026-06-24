Added [erdos936_powerful_search.py](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py), a standalone search tool for `2^n+1`, `2^n-1`, `n!+1`, and `n!-1`. The key split is: fast small-prime squarefree witnesses for the `2^n±1` families ([line 185](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py#L185)), and exact factorization with Miller-Rabin + Pollard rho for cases small enough to check directly ([line 68](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py#L68), [line 97](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py#L97), [line 119](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py#L119)). The CLI is at [line 349](/Users/patrickkavanagh/math/scripts/erdos936_powerful_search.py#L349).

Verification:
- `python3 -m py_compile scripts/erdos936_powerful_search.py`
- `python3 scripts/erdos936_powerful_search.py --family all --n-start 1 --n-end 20 --prime-bound 1000 --max-exact-bits 2048`
- `python3 scripts/erdos936_powerful_search.py --family fact-plus --n-start 1 --n-end 30 --max-exact-bits 4096`
- `python3 scripts/erdos936_powerful_search.py --family fact-minus --n-start 1 --n-end 30 --max-exact-bits 4096`
- Spot checks: `2^64+1`, `2^67-1`, `2^127-1` all came back not powerful with exact factorization.

Initial search results:
- `2^n+1`: only `n=3` hit in `1..200` under the tested settings.
- `2^n-1`: only `n=1` hit in `1..200` under the tested settings.
- `n!+1`: hits at `n=4,5,7` in `1..30` (`25`, `121`, `5041 = 71^2`).
- `n!-1`: only `n=2` hit in `1..30`; `n=1` gives `0`, which the script marks outside the positive-integer definition.

One constraint: creating a new git branch was blocked by sandbox permissions on `.git/refs`, so this was done on the existing worktree.