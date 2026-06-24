#!/usr/bin/env python3
"""Sweep many admissible D (gcd=1, sum>=1, all d>=3) and report cofiniteness threshold
N0(D,k) = largest missing value <= N, for k=1,2. Tests SUFFICIENCY of (gcd=1, sum>=1)."""
import sys, math
sys.path.insert(0,'.')
from reach import reachable

def largest_missing(D, k, N):
    r = reachable(D, k, N)
    last = -1
    for n in range(N, -1, -1):
        if not ((r>>n)&1):
            return n  # largest missing
    return -1  # none missing -> fully covered

def info(D):
    s = sum(1.0/(d-1) for d in D)
    g = D[0]
    for d in D[1:]: g = math.gcd(g,d)
    return s, g

# Admissible families: gcd=1, sum>=1, all d>=3
cases = [
    [3,4,7],          # the proven tight case, sum=1
    [3,4,5],          # sum=1/2+1/3+1/4=1.083, gcd=1
    [3,5,7],          # 1/2+1/4+1/6=0.9166 <1 -> NOT admissible (control)
    [3,4],            # 1/2+1/3=0.833 <1 (control, sub-threshold)
    [3,4,5,7],        # well over 1
    [4,5,6,7],        # 1/3+1/4+1/5+1/6=0.95 <1 (control)
    [3,5,8],          # 1/2+1/4+1/7=0.892<1 control
    [3,4,9],          # 1/2+1/3+1/8=0.958<1 control
    [3,4,6],          # gcd=1? gcd(3,4,6)=1; 1/2+1/3+1/5=1.033
    [3,5,9],          # gcd=1; 1/2+1/4+1/8=0.875 <1 control
    [4,5,7,9,11],     # gcd=1; sum?
    [5,6,7,8,9,10,11],# gcd=1; sum?
    [3,7,8],          # gcd=1; 1/2+1/6+1/7=0.809 control
    [3,4,8],          # gcd=1; 1/2+1/3+1/7=0.976 <1 control (just under!)
    [3,4,11],         # gcd=1; 1/2+1/3+1/10=0.933 control
]
N = 200000
print(f"{'D':<28}{'sum':>8}{'gcd':>5}  {'k=1 N0':>10}{'k=2 N0':>10}")
for D in cases:
    s,g = info(D)
    adm = (s>=1.0-1e-9 and g==1 and all(d>=3 for d in D))
    n1 = largest_missing(D,1,N)
    n2 = largest_missing(D,2,N)
    flag = "ADM" if adm else "ctrl"
    c1 = "COFIN" if n1>=0 and n1<N else ("?>=N" if n1>=N else "cofin")
    print(f"{str(D):<28}{s:>8.3f}{g:>5}  {n1:>10}{n2:>10}  [{flag}]")
