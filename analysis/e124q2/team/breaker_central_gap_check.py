from fractions import Fraction
# Cross-check: is the central gap N3->N4->N5 MONOTONE, or noisy? And does the GROW/DECAY classification
# flip with the central-third window choice [1/3,2/3] vs a tighter [0.4,0.6]? If the verdict depends on
# the exact window, neither gap is a robust discriminator.
def Cd_N(d,N):
    vals=[Fraction(0)]
    for j in range(1,N+1):
        p=Fraction(1,d**j); vals=vals+[v+p for v in vals]
    return sorted(set(vals))
def sumset_frac(D,N):
    res=[Fraction(0)]
    for d in D:
        C=Cd_N(d,N); new=set()
        for a in res:
            for c in C: new.add(a+c)
        res=sorted(new)
    return res
def scaled_gap(D,N,lo,hi):
    vals=sumset_frac(D,N); hull=vals[-1]
    reg=[v for v in vals if hull*lo<=v<=hull*hi]
    g=max(reg[i+1]-reg[i] for i in range(len(reg)-1))
    return float(g)*max(D)**N
import math
def excess(D): return float(sum(Fraction(1,d-1) for d in D))-1
fams=[(3,5,6,9),(3,5,7,9),(3,4,5)]
print("Window-sensitivity: does GROW/DECAY (N3->N5) flip with the central-window choice?")
for D in fams:
    print(f"  {D} ex={excess(D):+.3f}:")
    for lo,hi,name in [(Fraction(1,3),Fraction(2,3),"[1/3,2/3]"),(Fraction(2,5),Fraction(3,5),"[0.4,0.6]"),(Fraction(9,20),Fraction(11,20),"[0.45,0.55]")]:
        g=[scaled_gap(D,N,lo,hi) for N in [3,4,5]]
        tr="DECAY" if g[2]<g[0] else "GROW"
        print(f"     window {name:<12}: {g[0]:.3f},{g[1]:.3f},{g[2]:.3f}  {tr}")
