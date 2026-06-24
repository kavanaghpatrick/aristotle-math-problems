import numpy as np
from fractions import Fraction
def repset_atomsieve(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def firstmiss_above(D,N,lo=0):
    exc=np.flatnonzero(~repset_atomsieve(D,0,N))
    big=exc[exc>=lo]
    return (len(exc), int(exc[-1]) if len(exc) else 0, len(big))
# Hypothesis: as beta -> 1 from below, the first-exception scale EXPLODES (explains 3,4,11).
# Test families with beta in (0.8, 1.0), measure largest miss / density up to fixed N.
fams=[(3,4),(3,5),(3,4,13),(3,4,12),(3,4,11),(3,4,10),(3,5,7),(3,4,9)]
N=200_000_000
print(f"beta vs exceptional behavior at N={N} (k=0):")
for D in sorted(fams,key=lambda D:float(sum(Fraction(1,d-1) for d in D))):
    b=float(sum(Fraction(1,d-1) for d in D))
    c,m,_=firstmiss_above(D,N)
    dens=c/N
    print(f"  {str(D):<12} beta={b:.4f}  misses={c:>10}  max={m:>10}  density={dens:.2e}  {'cofinite-so-far' if c==0 else ''}")
