import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def two_base_maxgap(D,k,N):
    b,c=sorted(D)[:2]
    rep=atoms_repset((b,c),k,N)
    idx=np.flatnonzero(rep); dd=np.diff(idx)
    valid=[int(dd[i])-1 for i in range(len(dd)) if idx[i+1]<N//2]
    return max(valid) if valid else 0, b, c
# FIXED: use adequate N per k (need N >> c^k to see the real two-base gap structure)
print("=== INV-C2 k-dependence (FIXED N) ===")
for D in [(3,4,7),(3,4,5)]:
    b,c=sorted(D)[:2]
    print(f"  {D} (two smallest {b},{c}):")
    for k in [1,2,3]:
        N = 20_000_000 * (k)  # big enough; 3,4 gaps scale ~ (3*4)^k roughly
        N = max(N, 100*(c**k))
        N = min(N, 200_000_000)
        g,_,_=two_base_maxgap(D,k,N)
        print(f"     k={k}: two-base({b},{c}) max gap = {g}  (N={N}, c^k={c**k}, (bc)^k={ (b*c)**k})")
