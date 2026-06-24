import numpy as np
import sys
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
D=(3,4,11); k=1
# Scan progressively, reporting count + max + upper-half complement density (maverick's diagnostic)
for N in [300_000_000, 700_000_000, 1_200_000_000, 2_500_000_000]:
    exc=exceptional2(D,k,N)
    cnt=len(exc); mx=int(exc[-1]) if cnt else 0
    upper=int(np.sum(exc> N//2))
    # near 11^8=214358881 and 11^9=2357947691: any exc in [11^J - 11^(J-1), 11^J)?
    bands=[]
    for J in [7,8,9]:
        q=11**J; lo=q-11**(J-1)
        b=[int(e) for e in exc if lo<=e<q]
        if b: bands.append((J,len(b),max(b)))
    print(f"N={N:>13}: count={cnt} max={mx} upper_half={upper} bands(near 11^J)={bands}", flush=True)
    if mx < N//2 and N>=700_000_000:
        # check frozen
        pass
