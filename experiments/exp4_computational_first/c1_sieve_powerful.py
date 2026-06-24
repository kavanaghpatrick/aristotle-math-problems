"""
EXP4 Computational Phase C1: Enumerate ALL powerful numbers up to N=10^11.

Strategy: For powerful n, write n = a^2 * b^3 with rad(b) | a (Golomb).
Equivalently, iterate over (a, b) pairs where gcd-conditions allow.

But the cleanest computational form: ALL powerful numbers up to N are
exactly {a^2 * b^3 : a,b >= 1} INTERSECTED with the predicate is_powerful.
NOT a unique representation, but every powerful is captured.

For efficiency, we generate via: powerful_set = { a^2 b^3 : a, b >= 1, a^2 b^3 <= N, gcd(a, b)=1, ... }
The cleanest unique parametrization is "Golomb": every powerful n is UNIQUELY written
as n = a^2 b^3 with b squarefree. So:
  - iterate b over squarefree integers with b^3 <= N
  - for each, iterate a >= 1 with a^2 b^3 <= N
  - (a, b) is unique to n, and n is powerful.

To check squarefree we sieve.
"""

import time
from math import isqrt

N_BOUND = 10**11

def squarefree_sieve(M):
    """Mu(n) != 0 means squarefree. Return array of bools."""
    mu = bytearray(M + 1)
    for i in range(M + 1):
        mu[i] = 1
    p = 2
    while p * p <= M:
        if mu[p]:
            for j in range(p * p, M + 1, p * p):
                mu[j] = 0
        p += 1
    return mu

# B_BOUND: b^3 <= N => b <= N^(1/3) ~ 4641
B_BOUND = int(N_BOUND ** (1/3)) + 2
print(f"N = {N_BOUND}, B_BOUND = {B_BOUND}")

t0 = time.time()
mu = squarefree_sieve(B_BOUND)
print(f"  squarefree sieve to {B_BOUND} done in {time.time()-t0:.1f}s")

# Generate powerful numbers via (a, b)
powerful = []
t0 = time.time()
for b in range(1, B_BOUND + 1):
    if not mu[b]:
        continue
    b3 = b ** 3
    if b3 > N_BOUND:
        break
    a_max = isqrt(N_BOUND // b3) + 1
    a = 1
    while a <= a_max:
        n = a * a * b3
        if n <= N_BOUND:
            powerful.append(n)
        a += 1

print(f"  generated {len(powerful)} powerful numbers in {time.time()-t0:.1f}s (pre-sort)")
powerful.sort()
print(f"  sorted in {time.time()-t0:.1f}s")

# Sanity: should match A001694 density: |P(N)| ~ zeta(3/2)/zeta(3) * sqrt(N) ~ 2.1732 * sqrt(N)
expected = 2.1732 * (N_BOUND ** 0.5)
print(f"  |P(N)| / sqrt(N) = {len(powerful) / N_BOUND**0.5:.4f}  (expected ~2.1732)")
print(f"  total elapsed: {time.time()-t0:.1f}s")

# Save to disk (sparse binary form: each int up to 10^11 fits in 5 bytes, use 8)
import struct
out = "/Users/patrickkavanagh/math/experiments/exp4_computational_first/powerful_1e11.bin"
print(f"  saving to {out}...")
with open(out, "wb") as f:
    # Header: N_BOUND (8 bytes), count (8 bytes), then count*8 bytes
    f.write(struct.pack("<QQ", N_BOUND, len(powerful)))
    # Pack in chunks to avoid huge intermediate
    CHUNK = 100000
    for i in range(0, len(powerful), CHUNK):
        chunk = powerful[i:i+CHUNK]
        f.write(struct.pack(f"<{len(chunk)}Q", *chunk))
print(f"  saved ({len(powerful)*8 // (1024*1024)} MB)")
