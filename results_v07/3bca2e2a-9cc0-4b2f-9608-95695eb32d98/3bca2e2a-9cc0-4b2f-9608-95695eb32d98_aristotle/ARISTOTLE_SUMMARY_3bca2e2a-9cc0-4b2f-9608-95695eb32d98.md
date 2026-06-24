# Summary of changes
## Erdős-Straus Conjecture (Erdős Problem 242)

**File**: `RequestProject/ErdosStraus.lean`

**Status**: This is a famous **open conjecture** in number theory, verified computationally to 10^17 but with no known general proof. The main theorem `erdos_straus` remains `sorry`'d as expected for an open problem.

### What was proved

I proved the conjecture for all cases that are known to have elementary explicit solutions, covering the vast majority of integers:

1. **`erdos_straus_even`** — All even `n`: Uses the decomposition `4/n = 1/(n/2) + 1/n + 1/n`, i.e., witnesses `x = m, y = 2m, z = 2m` where `n = 2m`.

2. **`erdos_straus_3_mod_4`** — All `n ≡ 3 (mod 4)`: Uses the identity `4/n = 1/(k+2) + 1/((k+1)(k+2)) + 1/(n(k+1))` where `k = n/4`, derived from the fact that `4/n - 1/(k+1) = 1/(n(k+1))` when `n = 4k+3`.

3. **`erdos_straus_div_3`** — All `n` divisible by 3: Uses the decomposition `4/(3j) = 1/(j+1) + 1/(j(j+1)) + 1/(3j)`, which sums to `1/j + 1/(3j) = 4/(3j)`.

### What remains open

The only unresolved case is `n ≡ 1 (mod 4)` with `gcd(n, 6) = 1` (i.e., `n ≡ 1` or `5 (mod 12)`). This is precisely the hard case of the Erdős-Straus conjecture — it includes primes `p ≡ 1 (mod 4)` not divisible by 3, for which no uniform explicit construction is known. The three proved cases together cover all other positive integers ≥ 2.