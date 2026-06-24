Added [scripts/erdos828_search.py](/Users/patrickkavanagh/math/scripts/erdos828_search.py). It does a totient-sieve search for `phi(n) | (n+a)` and prints candidate family data.

Use it like:
```bash
python3 scripts/erdos828_search.py search --limit 200000 --a -1 0 1 2
python3 scripts/erdos828_search.py families --terms 5
```

What the search supports:
- `a = 0`: it reproduces the known family `n = 2^u 3^v`.
- `a = -1`: unconditional infinite family `n = p` prime, since `phi(p) = p - 1`.
- `a = 1`: up to `200000`, the nontrivial hits are `3, 15, 255, 65535`. This matches
  `n_k = ∏_{i<k} F_i = F_k - 2` with Fermat primes `F_i = 2^(2^i)+1`, giving `n_k + 1 = 2 phi(n_k)`.
  That is a good candidate family, but infinite only if enough Fermat primes exist.
- `a = 2`: up to `200000`, the nontrivial hits are `4, 6, 10, 30, 70, 510, 2590, 131070`.
  Two visible patterns are:
  `n = 2∏_{i<k} F_i`, which gives `n + 2 = 4 phi(n)`;
  and the chain `n = 2m_k`, `m_1 = 5`, `m_{k+1} = m_k(m_k+2)` when `m_k+2` is prime, which gives `10, 70, 2590, 3359230` with `n + 2 = 3 phi(n)`.

Verified with `python3 -m py_compile scripts/erdos828_search.py`. I also tried to create a git branch first, but the sandbox denied writes under `.git`, so I left the repo branch unchanged.