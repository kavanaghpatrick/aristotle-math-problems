import numpy as np
def repset_atomsieve(D,k,N):
    """Exact: rep[n]=True iff n is a subset-sum of atoms {d^j : d in D, j>=k, d^j<=N}, each once.
       This equals sum_{d} d^k B_d (distinct powers per base, bases distinct)."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N:
            atoms.append(d**j); j+=1
    for p in atoms:
        rep[p:]|=rep[:N+1-p].copy()  # OR-shift by atom p (use copy to avoid overlap aliasing)
    return rep
D=(3,4,11)
import time
for k in [0,1]:
    N=400_000_000
    t=time.time()
    rep=repset_atomsieve(D,k,N)
    exc=np.flatnonzero(~rep)
    cnt=len(exc); mx=int(exc[-1]) if cnt else 0
    upper=int(np.sum(exc>N//2))
    bands3=[]
    for m in range(10,18):
        q=3**m
        if q>N: break
        lo=q-3**(m-1); b=int(np.sum((exc>=lo)&(exc<q)))
        if b: bands3.append((m,b))
    print(f"k={k} N={N}: count={cnt} max_miss={mx} upper_half={upper} 3^m_bands={bands3} ({time.time()-t:.1f}s)", flush=True)
