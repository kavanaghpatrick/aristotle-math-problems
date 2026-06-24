I added a verifier at [scripts/erdos398_brocard_verify.py](/Users/patrickkavanagh/math/scripts/erdos398_brocard_verify.py#L1). It keeps `n!` modulo several primes just above `nmax`, discards any `n` for which `n!+1` is a non-residue modulo one of those primes, and runs exact `isqrt` only on the survivors.

In this environment I checked:
- `python3 scripts/erdos398_brocard_verify.py --nmax 100000 --filters 20`
  Result: only `n = 4, 5, 7` survive, and exact checking confirms those are the only solutions up to `10^5`.
- `python3 scripts/erdos398_brocard_verify.py --nmax 1000000 --filters 24 --print-candidates`
  Result: survivors are exactly `[4, 5, 7]`, so there are no solutions up to `10^6` beyond the classical ones.

Useful modular facts for `n! + 1 = m^2`:
- For every prime `p <= n`, `m^2 ≡ 1 (mod p)`, hence `m ≡ ±1 (mod p)`.
- More strongly, if `p` is odd and `p^a | n!`, then `m^2 ≡ 1 (mod p^a)`, so `m ≡ ±1 (mod p^a)`.
- Examples:
  - `n >= 6` gives `m ≡ ±1 (mod 9)`.
  - `n >= 10` gives `m ≡ ±1 (mod 25)`.
  - `n >= 14` gives `m ≡ ±1 (mod 49)`.
- Since `n! = (m-1)(m+1)`, for `n >= 2` we have `m` odd and `gcd(m-1,m+1)=2`. So every odd prime power dividing `n!` lies wholly in exactly one of `m-1` or `m+1`.
- For any prime `p` with `n/2 < p <= n`, we have `v_p(n!) = 1`, so exactly one of `m-1`, `m+1` is divisible by `p`.
- If `n = p-1` with `p` prime, Wilson gives `(p-1)! ≡ -1 (mod p)`, so `p | m`, hence actually `p^2 | (p-1)!+1`. Therefore any solution with `n+1` prime forces `n+1` to be a Wilson prime. This immediately rules out almost all cases of the form `n = p-1`.

What this does not prove is the full conjecture, but it gives a clean partial structure:
- local constraints on `m` modulo every prime power dividing `n!`,
- the factorization constraint `n! = (m-1)(m+1)`,
- the Wilson-prime obstruction when `n+1` is prime,
- and rigorous finite verification through `10^6`.

Verification I ran:
- `python3 -m py_compile scripts/erdos398_brocard_verify.py`
- `python3 scripts/erdos398_brocard_verify.py --nmax 100000 --filters 20`
- `python3 scripts/erdos398_brocard_verify.py --nmax 1000000 --filters 24 --print-candidates`

If you want, I can next add a short note deriving the Wilson-prime obstruction and the `m ≡ ±1 mod p^a` lemmas in a more theorem-proof style.