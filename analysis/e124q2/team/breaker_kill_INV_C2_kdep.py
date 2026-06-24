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
    """max gap of the two-smallest-base sumset b^k B_b + c^k B_c = the worst correction the rest must span.
    This is the REAL ledger bound (worst case, not nearest-below)."""
    b,c=sorted(D)[:2]
    rep=atoms_repset((b,c),k,N)
    idx=np.flatnonzero(rep); dd=np.diff(idx)
    # ignore boundary: gaps where both endpoints < N/2
    valid=[int(dd[i])-1 for i in range(len(dd)) if idx[i+1]<N//2]
    return max(valid) if valid else 0, b, c
# DECISIVE: does the two-base ledger bound (max gap) grow with k? If bounded-per-k but growing with k,
# it's the same MW content (per-fixed-k theorem only). If it grows like d^k, INV-C2 is NOT k-uniform.
print("=== INV-C2 k-dependence: two-base max gap (the ledger bound) vs k ===")
for D in [(3,4,7),(3,4,5)]:
    b,c=sorted(D)[:2]
    print(f"  {D} (two smallest {b},{c}):")
    for k in [1,2,3]:
        N=min(60_000_000, 200*max(D)**k)
        g,_,_=two_base_maxgap(D,k,N)
        print(f"     k={k}: two-base max gap = {g}  (~ b^k·const? b^k={b**k}, c^k={c**k})")
print("\nIf gap grows ~c^k (the larger of the two), the ledger B(D,k) grows with k => NOT k-uniform")
print("=> INV-C2 gives at best a per-fixed-k theorem, same as the wall. KILL for the uniform conjecture.")
