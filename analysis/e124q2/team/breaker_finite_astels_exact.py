import numpy as np
from fractions import Fraction
# EXACT finite-stage Astels central gap (no gridding). 
# C_d^(N) = {sum_{j=1}^{N} e_j d^{-j} : e_j in {0,1}}. Scale ALL bases by L = lcm-free common integer:
# represent each c in C_d^(N) exactly as Fraction. Sumset over D, find max gap in the central region.
# To make it integer-exact, multiply by P = prod_d d^N? Too big. Instead use Fraction and sort.
def Cd_N(d,N):
    """finite depth-N Cantor approx of C_d as sorted list of Fractions in [0, sum d^-j]."""
    vals=[Fraction(0)]
    for j in range(1,N+1):
        p=Fraction(1,d**j)
        vals=vals+[v+p for v in vals]
    return sorted(set(vals))
def sumset_frac(D,N):
    res=[Fraction(0)]
    for d in D:
        C=Cd_N(d,N)
        new=set()
        for a in res:
            for c in C:
                new.add(a+c)
        res=sorted(new)
    return res
def max_central_gap(vals, lo_frac=0.2, hi_frac=0.8):
    """max gap in the central region [lo_frac*hull, hi_frac*hull]."""
    hull=vals[-1]
    lo=hull*Fraction(lo_frac).limit_denominator(); hi=hull*Fraction(hi_frac).limit_denominator()
    central=[v for v in vals if lo<=v<=hi]
    if len(central)<2: return None
    g=max(central[i+1]-central[i] for i in range(len(central)-1))
    return g, hull
from math import log
print("EXACT finite-stage central gap of sumset_d C_d^(N), scaled gap = gap * d_max^N:")
print("(maverick v4: scaled gap <1 => gap-free integer seed => cofinite. Strict excess should give <1.)")
for D in [(3,4,5),(3,4,5,7),(3,5,7,9),(3,4,7),(3,5,7,13)]:
    dmax=max(D)
    b=float(sum(Fraction(1,d-1) for d in D)); ex=b-1
    row=f"  {str(D):<14} β={b:.3f} ex={ex:+.3f}: "
    for N in [3,4,5]:
        try:
            g,hull=max_central_gap(sumset_frac(D,N))
            scaled=float(g)*dmax**N
            row+=f"N{N}:{scaled:.3f} "
        except Exception as e:
            row+=f"N{N}:ERR "
    print(row)
