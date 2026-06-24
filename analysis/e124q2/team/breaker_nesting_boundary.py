import numpy as np
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for p in atoms_list(D,k,N): rep[p:]|=rep[:N+1-p].copy()
    return rep
def chain_high_theta(n,D,k,N,full,allatoms,thr=0.8):
    """peel min-top-atom recursion; count how many levels are high-θ (>thr). Returns count + ok."""
    rem=n; cnt=0; guard=0
    while rem>0 and guard<400:
        guard+=1
        # peel: choose atom a<=rem s.t. (rem-a) representable; track theta=a/rem for the MIN such top atom
        # use largest valid a (consistent with INV-C1); theta=a/rem
        placed=False
        for a in reversed([x for x in allatoms if x<=rem]):
            if full[rem-a]:
                if a/rem>thr: cnt+=1
                rem-=a; placed=True; break
        if not placed: return cnt, False
    return cnt, True
# Boundary family (3,4,7) ∑=1, push k=4 (and k=5 if reachable). Does single-peel localization hold?
print("=== BOUNDARY ∑=1 (3,4,7) high-k cascade test (modular's decisive ask) ===")
for k in [3,4]:
    N=min(180_000_000, 300*7**k)  # need above threshold; 7^4=2401, threshold ~ d_max^k scale
    # (3,4,7) thresholds: k=3 ~166M; k=4 huge. So at reachable N for k=4 we are BELOW threshold -> few misses
    full=atoms_repset((3,4,7),k,N); allatoms=atoms_list((3,4,7),k,N)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    # sample representable n in top region
    lo=max(n0+1, N//2); hi=min(lo+8000,N)
    maxchain=0; nhigh=0
    for n in range(lo,hi):
        if not full[n]: continue
        c,ok=chain_high_theta(n,(3,4,7),k,N,full,allatoms)
        if c>0: nhigh+=1
        maxchain=max(maxchain,c)
    print(f"  (3,4,7) k={k}: N={N} n0={n0} window[{lo},{hi}]: MAX high-θ chain levels={maxchain}, #n with any high-θ={nhigh}")
print("\nSURVIVES if max chain stays O(1) (single-scale obstruction) even at boundary high-k.")
