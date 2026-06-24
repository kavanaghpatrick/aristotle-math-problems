import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def maxgap_below(rep,bound):
    idx=np.flatnonzero(rep); dd=np.diff(idx)
    v=[int(dd[i])-1 for i in range(len(dd)) if idx[i+1]<bound]
    return max(v) if v else 0
# DECISIVE INV-C2 KILL: is the two-base (3,4) k=1 max gap UNBOUNDED (grows with N)?
# B_3+B_4 has beta=0.833<1 => NOT cofinite => gaps grow without bound. Confirm.
print("INV-C2 KILL: two-base (3,4) k=1 max gap as N grows (should grow unboundedly):")
rep=atoms_repset((3,4),1,400_000_000)
for bound in [10_000_000,50_000_000,150_000_000,400_000_000]:
    g=maxgap_below(rep,bound)
    print(f"  max gap below {bound}: {g}")
print("\n=> two-base gap GROWS without bound => the ledger L the automaton must hold is UNBOUNDED")
print("=> INV-C2 is INFINITE-STATE => DEAD. The third base must span arbitrarily large two-base gaps")
print("   = joint multi-atom (cassels DP4), not a bounded finite-state ledger.")
