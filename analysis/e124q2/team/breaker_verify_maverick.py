import numpy as np
from fractions import Fraction
def repset_atoms(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def strict_n0(D,k,Nmax=4_000_000_000):
    hist=[];N=2_000_000
    while N<=Nmax:
        exc=np.flatnonzero(~repset_atoms(D,k,N)); c=len(exc); mx=int(exc[-1]) if c else 0
        hist.append((c,mx,N))
        if len(hist)>=3 and hist[-1][0]==hist[-2][0]==hist[-3][0] and hist[-2][1]<hist[-2][2]//2 and hist[-1][1]<hist[-1][2]//2:
            return mx
        N*=2
    return None
def beta(D): return float(sum(Fraction(1,d-1) for d in D))
# maverick v6 claim: n0(k=2) for strict {3,4,5}=? boundary {3,4,7}=3982888. And the EXCESS hypothesis:
# does strict excess => effectively SMALLER thresholds than boundary at same scale?
print("maverick's strict-vs-boundary threshold dichotomy (integer ground truth):")
print(f"{'D':<14}{'β':>8}{'excess':>9}{'n0(k=1)':>9}{'n0(k=2)':>11}{'n0(k=3)':>12}")
for D in [(3,4,7),(3,4,5),(3,4,5,7),(3,5,7,9),(3,5,7,13)]:
    b=beta(D); ex=b-1
    n1=strict_n0(D,1); n2=strict_n0(D,2); n3=strict_n0(D,3)
    print(f"{str(D):<14}{b:>8.3f}{ex:>9.3f}{str(n1):>9}{str(n2):>11}{str(n3):>12}")
print("\nmaverick v6 honest claim: n0(k+1)/n0(k) super-exp for BOTH strict & boundary, doesn't separate:")
for D in [(3,4,5),(3,4,7)]:
    n1=strict_n0(D,1);n2=strict_n0(D,2);n3=strict_n0(D,3)
    print(f"  {D}: n2/n1={n2/n1:.0f} n3/n2={n3/n2:.0f}")
