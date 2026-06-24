#!/usr/bin/env python3
"""
Reachable set R(D,k,N) = { n <= N : n in sum_{d in D} d^k * B_d }, via bitset (big-int) DP.
Bit i set <=> i reachable. Minkowski sum of two bitsets A,B capped at N:
  result = OR over set bits j of B of (A << j), masked to N+1 bits.
We iterate over the SMALLER set's bits for speed. Adding distinct powers to one base:
  reach |= reach << p   (each power used at most once -> process powers one at a time,
  but since within a base powers are distinct we OR-shift; standard 0/1 knapsack via bitset:
  for each power p: reach |= reach << p, then mask).
"""
import sys, math

def base_set_bits(d, k, N):
    """Bitset of A_d = { sums of distinct d^j, j>=k } intersect [0,N]."""
    mask = (1 << (N+1)) - 1
    reach = 1  # bit 0 set (empty sum = 0)
    j = k
    while d**j <= N:
        p = d**j
        reach |= (reach << p)
        reach &= mask
        j += 1
    return reach

def mink(a, b, N):
    mask = (1 << (N+1)) - 1
    # iterate over set bits of whichever has fewer
    ca, cb = bin(a).count("1"), bin(b).count("1")
    if cb < ca:
        a, b = b, a
    out = 0
    bb = b
    j = 0
    while bb:
        if bb & 1:
            out |= (a << j)
        bb >>= 1
        j += 1
    return out & mask

def reachable(D, k, N):
    cur = base_set_bits(D[0], k, N)
    for d in D[1:]:
        cur = mink(cur, base_set_bits(d, k, N), N)
    return cur

def analyze(D, k, N, show=40):
    r = reachable(D, k, N)
    missing = [n for n in range(N+1) if not ((r >> n) & 1)]
    sm = sum(1.0/(d-1) for d in D)
    g = D[0]
    for d in D[1:]:
        g = math.gcd(g, d)
    print(f"D={D} k={k} N={N}  sum 1/(d-1) = {sm:.4f}  gcd={g}")
    if missing:
        print(f"  #missing <= {N}: {len(missing)}   largest missing: {missing[-1]}")
        print(f"  missing tail (last {show}): {missing[-show:]}")
    else:
        print(f"  FULLY COVERED [0,{N}]: no missing values")
    return missing

if __name__ == "__main__":
    import ast
    D = ast.literal_eval(sys.argv[1]); k = int(sys.argv[2]); N = int(sys.argv[3])
    analyze(D, k, N)
