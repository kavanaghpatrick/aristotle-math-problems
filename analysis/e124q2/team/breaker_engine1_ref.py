import sys
from fractions import Fraction

def per_base_mask(d, k, N):
    """Bitmask (Python int) over [0,N] of x in sumsOfDistinctPowers(d,k):
       x = sum of distinct d^j, j>=k.  bit i set <=> i representable, i<=N."""
    # Start with {0} (empty sum).
    mask = 1  # bit 0
    j = k
    while d**j <= N:
        p = d**j
        # For each existing representable x, x+p is representable (distinct powers: each power used once)
        # Since we add powers in increasing j and each at most once, shifting mask by p and OR is correct
        # but must cap at N.
        shifted = (mask << p)
        # keep only bits <= N
        shifted &= (1 << (N+1)) - 1
        mask |= shifted
        j += 1
    return mask

def sumset_mask(masks, N):
    """Pointwise sumset over list of per-base masks, capped at N."""
    full = (1 << (N+1)) - 1
    res = masks[0] & full
    for m in masks[1:]:
        # convolution via shifting: for each set bit position p in m, OR (res<<p)
        # but m is huge; iterate over set bits of the SMALLER operand
        # Use the trick: new = OR over bits p of m of (res<<p)
        # To bound cost, iterate bits of m
        new = 0
        mm = m
        while mm:
            p = (mm & -mm).bit_length() - 1
            new |= (res << p)
            mm &= mm - 1
        res = new & full
    return res

def admissible(D, k):
    s = sum(Fraction(1, d-1) for d in D)
    import math
    g = 0
    for d in D:
        g = math.gcd(g, d)
    return all(d>=3 for d in D) and s >= 1 and g == 1, s, g

def exceptional(D, k, N):
    masks = [per_base_mask(d, k, N) for d in D]
    rep = sumset_mask(masks, N)
    full = (1 << (N+1)) - 1
    miss = (~rep) & full
    # list missing n
    out = []
    mm = miss
    while mm:
        p = (mm & -mm).bit_length() - 1
        out.append(p)
        mm &= mm - 1
    return out

if __name__ == "__main__":
    # quick sanity: (3,4,7) known TRUE for all k!=0 -> exceptional set should be finite (die out)
    for k in [1,2]:
        D=(3,4,7)
        ok,s,g = admissible(D,k)
        N=20000
        exc = exceptional(D,k,N)
        print(f"D={D} k={k} admissible={ok} sum={s} gcd={g} #exc<= {N}: {len(exc)} max_exc={max(exc) if exc else None}")

def report(D,k,N,show=20):
    ok,s,g=admissible(D,k)
    exc=exceptional(D,k,N)
    tail=[e for e in exc if e> N*0.8]
    print(f"D={D} k={k} adm={ok} sum={s} gcd={g} N={N} #exc={len(exc)} max={max(exc) if exc else None} | tail(>0.8N)={len(tail)} top:{sorted(exc)[-show:]}")
