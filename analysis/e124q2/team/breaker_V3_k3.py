import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
# INV-V3 decisive: (3,4,7) k=3, max miss=166,025,260. Do holes-per-band re-spike after draining?
# Check BOTH 7-bands and 4-bands up to past 166M.
D=(3,4,7); k=3; N=200_000_000
exc=np.flatnonzero(~atoms_repset(D,k,N))
excs=exc  # numpy
print(f"(3,4,7) k=3, total misses={len(exc)}, max={int(exc[-1])}")
for base,label in [(7,"7"),(4,"4"),(3,"3")]:
    print(f"  holes per {label}^j band:")
    bands=[]
    for j in range(2,18):
        lo=base**j; hi=base**(j+1)
        if lo>N: break
        h=int(np.sum((excs>=lo)&(excs<hi)))
        bands.append((j,h))
    # detect re-spike: a zero (or near-zero) band followed by a larger band
    seq=[h for _,h in bands]
    respike=any(seq[i]==0 and any(s>0 for s in seq[i+1:]) for i in range(len(seq)))
    nonzero=[(j,h) for j,h in bands if h>0]
    print(f"     nonzero bands (j,holes): {nonzero}")
    print(f"     RE-SPIKE (zero band then holes return)? {respike}")
