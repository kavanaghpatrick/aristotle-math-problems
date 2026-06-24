import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def maxgap_below(D,k,N,bound):
    rep=atoms_repset(D,k,N); idx=np.flatnonzero(rep); dd=np.diff(idx)
    v=[(int(dd[i])-1, int(idx[i])+1) for i in range(len(dd)) if idx[i+1]<bound]
    return max(v) if v else (0,0)
print("INV-C2 KILL: two-base (3,4) k=1 max gap GROWS with N => unbounded ledger:")
for N in [20_000_000, 80_000_000]:
    g,pos=maxgap_below((3,4),1,N,N*9//10)
    print(f"  N={N}: max two-base gap = {g} (at n~{pos})")
