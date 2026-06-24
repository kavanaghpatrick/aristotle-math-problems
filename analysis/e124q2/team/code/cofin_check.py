import sys
from math import gcd
from functools import reduce

def powers_bitset(d, k, N):
    # bitset (python int) of d^k*B_d cap [0,N]: sums of distinct d^j, j>=k
    reach = 1  # bit0 set = {0}
    j = k
    while d**j <= N:
        p = d**j
        # reach |= reach << p, then mask to N+1 bits
        reach |= (reach << p)
        reach &= (1 << (N+1)) - 1
        j += 1
    return reach

def sumset_bitset(D, k, N):
    cur = 1
    for d in D:
        s = powers_bitset(d, k, N)
        # Minkowski: cur = OR over set bits of s of (cur << bit). Equivalent: convolve supports.
        # Do it by: new = 0; for each set bit b in s: new |= cur << b; but s huge. Instead iterate cur's bits if smaller.
        # Use the standard trick: result bit n set iff exists a+b=n. We do OR of shifts by the SMALLER operand's bits.
        # pick smaller popcount
        new = 0
        # iterate over set bits of s (the per-base summand) -- but that can be many.
        # Better: iterate over set bits of cur if cur sparse, else s. Use s's bits via its powers structure is sparse early.
        a, bset = (cur, s)
        # iterate bits of bset
        bb = bset
        while bb:
            low = bb & (-bb)
            bit = low.bit_length()-1
            new |= (a << bit)
            bb ^= low
        new &= (1 << (N+1)) - 1
        cur = new
    return cur

def largest_missing(D, k, N):
    r = sumset_bitset(D, k, N)
    full = (1 << (N+1)) - 1
    missing = full & ~r
    if missing == 0:
        return -1, 0
    lm = missing.bit_length()-1
    cnt = bin(missing).count('1')
    return lm, cnt

if __name__ == "__main__":
    D = tuple(int(x) for x in sys.argv[1].split(','))
    k = int(sys.argv[2])
    N = int(sys.argv[3])
    lm, cnt = largest_missing(D, k, N)
    print(f"D={D} k={k} N={N}: largest_missing={lm} count={cnt}")
