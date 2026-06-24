import numpy as np
from fractions import Fraction
from math import gcd
def repset_atoms(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def strict_n0(D,k,Nmax=4_000_000_000):
    hist=[];N=4_000_000
    while N<=Nmax:
        exc=np.flatnonzero(~repset_atoms(D,k,N)); c=len(exc); mx=int(exc[-1]) if c else 0
        hist.append((c,mx,N))
        if len(hist)>=3 and hist[-1][0]==hist[-2][0]==hist[-3][0] and hist[-2][1]<hist[-2][2]//2 and hist[-1][1]<hist[-1][2]//2:
            return 'FINITE', mx, N
        N*=2
    c,mx,N=hist[-1]
    return f'UNSETTLED(cnt={c})', mx, N
def adm(D):
    s=sum(Fraction(1,d-1) for d in D); g=0
    for d in D: g=gcd(g,d)
    return float(s),g
# scholar's two-prime-power (2^a/3^b) admissible families
fams=[(3,4,8,9),(3,4,8,32),(3,4,8,27),(3,4,9,16),(3,4,9,27,81)]
print("scholar's two-prime-power admissible families (all bases 2^a or 3^b) — strict cofiniteness:")
for D in fams:
    s,g=adm(D)
    print(f"\nD={D} β={s:.4f} gcd={g} admissible={s>=1 and g==1}")
    for k in [1,2,3]:
        st,n0,N=strict_n0(D,k)
        print(f"   k={k}: {st}  n0={n0}  (@N={N})")
