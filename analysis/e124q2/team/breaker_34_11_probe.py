# Memory-light: directly test representability of specific n for (3,4,11) k=1 WITHOUT full bitset.
# n = a3 + a4 + a11, a_d in S(d,1) (0/1 digits base d, lowest digit 0). Meet-in-middle:
# enumerate a11 in S(11,1) <= n (few, since 11^j sparse), then test (n - a11) in S(3,1)+S(4,1).
# For S(3,1)+S(4,1) membership we still need a set, but only up to n - smallest a11. Use a windowed
# bitset of S(3,1)+S(4,1) up to n (n ~ 2.3e9 -> 2.3Gbit = 290MB bool... borderline). 
# Better: test (n-a11) = a3+a4 by enumerating a3 in S(3,1) <= n-a11 and checking (n-a11-a3) in S(4,1).
# S(3,1) up to 2.3e9 has ~2^19 elements (powers 3^1..3^19, subset sums) = 500K, manageable as a set.
import numpy as np
def S_d1_set(d, N):
    """set of 0/1-digit base-d numbers with lowest digit 0 (j>=1), <= N."""
    vals=[0]; j=1
    while d**j<=N:
        p=d**j; vals=vals+[v+p for v in vals if v+p<=N]; j+=1
    return set(vals)
def in_S_d1(x,d):
    if x<0: return False
    pos=0
    while x>0:
        dig=x%d
        if dig not in (0,1): return False
        if pos==0 and dig!=0: return False
        x//=d; pos+=1
    return True
def representable(n):
    S11=[a for a in S_d1_set(11,n)]  # ~ up to 2^9
    S3=S_d1_set(3,n)
    for a11 in S11:
        rem1=n-a11
        for a3 in S3:
            if a3>rem1: continue
            if in_S_d1(rem1-a3,4): return True
    return False
# Probe band just below 11^9 = 2357947691, and a few control points
import sys
targets=[]
q=11**9
# sample 200 points in [q - 11^8, q)
import random
random.seed(1)
band=[q-1-i for i in range(0,11**8,11**8//200)]
miss=[]
for n in band[:200]:
    if not representable(n): miss.append(n)
print(f"(3,4,11) k=1, band just below 11^9={q}: tested {len(band[:200])} points, {len(miss)} non-representable")
if miss: print("  misses:", miss[:20])
# control: known small misses should be caught; test 1595 (cassels' N0) and a representable
print("  sanity in_S checks: 1595 representable?", representable(1595), "| 1000000 representable?", representable(1000000))
