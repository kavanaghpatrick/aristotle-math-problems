# Erdős Problem 203 (computational exploration)

Problem: find a positive integer `m` with `gcd(m,6)=1` such that

`2^k * 3^l * m + 1`

is **never prime** for any `k,l >= 0`.  A standard approach is a **finite covering** by primes `p>3`:
choose, for each prime `p`, a residue `m ≡ r_p (mod p)` so that for every pair `(k,l)` at least one `p`
divides `2^k 3^l m + 1`.

Status: this is currently listed as **OPEN** (research problem), so this folder contains tooling to:

- compute `ord_p(2)` and `ord_p(3)` for primes `p`
- compute the `(k mod ord_p(2), l mod ord_p(3))` classes covered by a fixed `m mod p`
- run finite-modulus covering searches (i.e. prove compositeness for all `(k,l)` in a periodic box)

## Quick start

```bash
python experiments/erdos203/erdos203_cover.py orders --prime-limit 200
python experiments/erdos203/erdos203_cover.py classes --p 73
python experiments/erdos203/erdos203_cover.py greedy --primes 5,7,11,13,17,19,23 --max-cells 40000000
```

The `greedy` subcommand attempts a set-cover style search on the fundamental domain
`K = lcm(ord_p(2))`, `L = lcm(ord_p(3))` (restricted by `--max-cells`).

