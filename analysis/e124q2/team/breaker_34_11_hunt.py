import numpy as np, time
# Push (3,4,11) k=0 as far as memory allows using packed bits (8x denser) to find first exception.
# Use np.packbits-style: represent rep as uint8 bit-packed? Simpler: bool array, go to ~12e9 if RAM allows.
# bool = 1 byte/elt. 12e9 bytes = 12GB — too much. Use the structure: any miss must be reachable;
# instead scan WINDOWS. Use sliding-window DP: but atoms up to N needed. For k=0 the atoms are global.
# Best feasible: bool to ~6e9 (6GB). Try incrementally.
def repset(D,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=0
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
D=(3,4,11)
for N in [6_000_000_000, 9_000_000_000]:
    t=time.time()
    try:
        rep=repset(D,N)
        exc=np.flatnonzero(~rep)
        c=len(exc); m=int(exc[-1]) if c else 0
        print(f"k=0 (3,4,11) N={N}: misses={c} max={m} ({time.time()-t:.0f}s)", flush=True)
        del rep, exc
    except MemoryError:
        print(f"N={N}: MemoryError - stopping", flush=True); break
