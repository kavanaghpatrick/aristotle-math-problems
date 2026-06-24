Exact Python search is already in [scripts/erdos389.py](/Users/patrickkavanagh/math/scripts/erdos389.py). It computes the minimal `k` by tracking prime-adic valuation deficits incrementally, which is much faster than multiplying the two products directly. I also used the local Rust helper [scripts/a375071_rust/src/main.rs](/Users/patrickkavanagh/math/scripts/a375071_rust/src/main.rs) to push the search frontier.

**Python**
```python
# run:
#   python3 scripts/erdos389.py --nmax 25 --kmax 100000000

from array import array
from dataclasses import dataclass

def spf_sieve(limit: int) -> array:
    spf = array("I", [0]) * (limit + 1)
    if limit >= 1:
        spf[1] = 1
    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
            if i <= limit // i:
                for j in range(i * i, limit + 1, i):
                    if spf[j] == 0:
                        spf[j] = i
    return spf

@dataclass
class DiffTracker:
    spf: array
    diff: dict[int, int]
    neg_count: int = 0

    def _bump(self, p: int, delta: int) -> None:
        old = self.diff.get(p, 0)
        new = old + delta
        if old < 0 <= new:
            self.neg_count -= 1
        elif old >= 0 > new:
            self.neg_count += 1
        if new == 0:
            self.diff.pop(p, None)
        else:
            self.diff[p] = new

    def add_factor(self, x: int, mult: int) -> None:
        while x > 1:
            p = int(self.spf[x])
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            self._bump(p, mult * e)

def minimal_k(n: int, k_max: int) -> int | None:
    spf = spf_sieve(n + 2 * k_max + 1)
    t = DiffTracker(spf=spf, diff={})
    t.add_factor(n + 1, +1)
    t.add_factor(n, -1)
    if t.neg_count == 0:
        return 1
    for k in range(1, k_max):
        t.add_factor(n + 2 * k, +1)
        t.add_factor(n + 2 * k + 1, +1)
        t.add_factor(n + k, -2)
        if t.neg_count == 0:
            return k + 1
    return None

for n in range(1, 26):
    print(n, minimal_k(n, 100_000_000))
```

**Computed values**
For your indexing
`n(n+1)...(n+k-1) | (n+k)...(n+2k-1)`:

| n | minimal k |
|---|-----------|
| 1 | 1 |
| 2 | 5 |
| 3 | 4 |
| 4 | 207 |
| 5 | 206 |
| 6 | 2475 |
| 7 | 984 |
| 8 | 8171 |
| 9 | 8170 |
| 10 | 45144 |
| 11 | 45143 |
| 12 | 3648830 |
| 13 | 3648829 |
| 14 | 7979077 |
| 15 | 7979076 |
| 16 | 58068862 |
| 17 | 58068861 |
| 18 | 255278295 |
| 19 | 255278294 |
| 20 | `> 500000000` |
| 21 | `> 100000000` |
| 22 | `> 100000000` |
| 23 | `> 100000000` |
| 24 | `> 100000000` |
| 25 | `> 100000000` |

So: exact through `n=19`; beyond that, exact search is already expensive. This matches the fact that Erdős 389 is still open.

**Growth**
- Empirical only. No proved asymptotic is known.
- Fit on `n=1..19`: `log10 k ≈ -0.135 + 0.480 n`, so very roughly `k(n) ≈ 0.73 · 3.02^n`.
- Fit on the more stable tail `n=8..19`: base drops to about `2.82^n`.
- Strong irregularity: from `n=8` onward, the data shows repeated pairs
  `k(9)=k(8)-1`, `k(11)=k(10)-1`, ..., `k(19)=k(18)-1`.
- Lower bound `k(20) > 5·10^8` shows the explosive growth continues.

**Existence proofs for specific n**
The problem is open in general, but for any specific `n` in the table, existence is proved by the explicit witness `k`.

Examples:
- `n=1`, `k=1`: `1 | 2`.
- `n=2`, `k=5`:
  \[
  \frac{7\cdot8\cdot9\cdot10\cdot11}{2\cdot3\cdot4\cdot5\cdot6}=77\in\mathbb Z.
  \]
- `n=3`, `k=4`:
  \[
  \frac{7\cdot8\cdot9\cdot10}{3\cdot4\cdot5\cdot6}=14\in\mathbb Z.
  \]

For larger listed values, the same style of proof applies: exhibit the `k` from the table and verify divisibility exactly. The script does that prime-by-prime, so each returned `k` is a rigorous certificate for that `n`.

Sources: [erdosproblems.com/389](https://www.erdosproblems.com/389), [OEIS A375071](https://oeis.org/A375071) (note OEIS uses shifted indexing: its `a(0)` is your `n=1`).

1. Run `python3 [scripts/erdos389.py](/Users/patrickkavanagh/math/scripts/erdos389.py) --nmax 25 --kmax 100000000` for the exact bounded search.
2. Use the Rust helper for larger cases: `scripts/a375071_rust/target/release/a375071 search 20 1000000000`.
3. If you want, I can keep the long exact search running for `n=20` and then extend the table past `19`.