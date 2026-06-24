import numpy as np, time
def repset_atomsieve(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms:
        rep[p:]|=rep[:N+1-p].copy()
    return rep
D=(3,4,11)
# Push k=0 far. 4GB bool = 4e9. Try up to ~4.5e9 (covers 11^9=2.36B, 3^20=3.49B, 4^16=4.29B).
for N in [1_000_000_000, 2_500_000_000, 4_500_000_000]:
    t=time.time()
    try:
        rep=repset_atomsieve(D,0,N)
        exc=np.flatnonzero(~rep)
        c=len(exc); m=int(exc[-1]) if c else 0
        print(f"k=0 (3,4,11) N={N}: count={c} max_miss={m} ({time.time()-t:.1f}s)", flush=True)
        del rep
    except MemoryError:
        print(f"N={N}: MemoryError"); break
