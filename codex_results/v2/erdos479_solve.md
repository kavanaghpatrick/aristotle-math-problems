Implemented [scripts/erdos479_search.py](/Users/patrickkavanagh/math/scripts/erdos479_search.py). It does a one-pass scan of `pow(2, n, n)` for `n <= 10^6`, then analyzes each hit via the odd-part multiplicative order `ord_m(2)` where `n = 2^a m`. I verified it with `python3 -m py_compile` and ran the full search; the `10^6` scan took about 9.4 seconds.

Counts up to `n = 10^6`:
`2: 78744, 3: 0, 4: 41903, 5: 1, 6: 1, 7: 2, 8: 29050, 9: 0, 10: 3, 11: 1, 12: 3, 13: 1, 14: 3, 15: 2, 16: 22567, 17: 3, 18: 15, 19: 2, 20: 1`.

Main patterns:
- Writing `n = 2^a m` with `m` odd, every hit satisfied `a <= v2(k)` and `gcd(m, k) = 1`. The script checks this directly.
- On the odd part, hits are controlled by multiplicative order: `2^n ≡ k (mod m)` means `n` falls into a discrete-log residue class modulo `ord_m(2)`. The script prints `ord_m(2)` and `n mod ord_m(2)` for sample hits.
- Only `k = 2, 4, 16` show a genuine large-prime family of shape `n = 2^a p`: tail counts are `78497`, `41536`, `22038`. This is exactly the order argument `2^(2^a p) ≡ 2^(2^a) (mod p)`.
- `k = 8` is the standout composite case: `29050` hits, almost all odd composites. For odd `n > 8`, this becomes the shifted pseudoprime condition `ord_n(2) | n - 3`.
- Prime solutions only appeared for `k = 2`. For prime `p`, Fermat gives `2^p ≡ 2 (mod p)`, so a prime solution for general `k` forces `p | (k - 2)`.

Run it with:
```bash
python3 scripts/erdos479_search.py --limit 1000000 --show 6
```

If you want, I can add CSV output or a second script that groups the `k=8` hits by factorization/order type.