import numpy as np
from fractions import Fraction
from math import gcd
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def exceptional2(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return np.flatnonzero(~rep)
def strict_n0(D,k,Nmax=2_000_000_000):
    """Returns (status, n0, N). status: 'FINITE' (2-doubling freeze, max<N/2) or 'OPEN' (not settled)."""
    hist=[];N=2_000_000
    while N<=Nmax:
        exc=exceptional2(D,k,N); cnt=len(exc); mx=int(exc[-1]) if cnt else 0
        hist.append((cnt,mx,N))
        if len(hist)>=3 and hist[-1][0]==hist[-2][0]==hist[-3][0] and hist[-2][1]<hist[-2][2]//2 and hist[-1][1]<hist[-1][2]//2:
            return 'FINITE', mx, N
        N*=2
    # not settled: report current count/density to judge
    c,mx,N=hist[-1]
    return f'UNSETTLED(count={c},dens={c/N:.3f})', mx, N
def admis(D):
    s=sum(Fraction(1,d-1) for d in D); g=0
    for d in D: g=gcd(g,d)
    return float(s), g, all(d>=3 for d in D)

fams=[(3,4,8,9),(3,4,8,32),(3,4,8,27),(3,4,9,16),(3,4,9,27,81)]
print("scholar's two-prime-power (2^a / 3^b) admissible families — strict cofiniteness test:")
for D in fams:
    s,g,ok=admis(D)
    print(f"\nD={D}  sum={s:.4f} gcd={g} admissible={s>=1 and g==1 and ok}")
    for k in [1,2,3]:
        status,n0,N=strict_n0(D,k)
        print(f"   k={k}: {status}  n0={n0}  (verified@N={N})")
