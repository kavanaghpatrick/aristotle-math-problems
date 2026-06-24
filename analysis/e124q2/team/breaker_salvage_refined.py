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
def recursion_thetas(n,D,k,N,full,allatoms):
    thetas=[]; rem=n; guard=0
    while rem>0 and guard<300:
        guard+=1; placed=False
        for a in reversed([x for x in allatoms if x<=rem]):
            if (rem-a)>=0 and full[rem-a]:
                thetas.append(a/rem); rem-=a; placed=True; break
        if not placed: return thetas,False
    return thetas,True
# REFINED: exclude terminal steps where rem is itself a single atom (θ=1 trivially). Measure the
# max NUMBER of consecutive levels with θ>0.9 EXCLUDING the final atom-hit. A genuine cascade =
# the recursion keeps landing just-above-a-power at successively smaller scales (nesting).
print("=== REFINED salvage: deepest consecutive-high-θ run (excluding trivial terminal atom-hit) ===")
for D,k,N in [((3,4,5),2,8_000_000),((3,4,5),3,12_000_000),((3,5,7,9),2,8_000_000)]:
    full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N); atomset=set(allatoms)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+5000,N)
    maxcascade=0; cascade_hist={}
    for n in range(lo,hi):
        if not full[n]: continue
        th,ok=recursion_thetas(n,D,k,N,full,allatoms)
        # drop the terminal step(s) where the remainder was a single atom (θ=1 trivial)
        th_nontrivial=[t for t in th if t<0.999]
        consec=0;mx=0
        for t in th_nontrivial:
            if t>0.9: consec+=1; mx=max(mx,consec)
            else: consec=0
        maxcascade=max(maxcascade,mx)
        cascade_hist[mx]=cascade_hist.get(mx,0)+1
    print(f"  {D} k={k}: deepest non-trivial θ>0.9 cascade = {maxcascade} levels; histogram(depth:count)={dict(sorted(cascade_hist.items()))}")
print("\nCascade depth O(1) & SHALLOW (mostly 0-1) => no nesting-at-every-scale => salvage SURVIVES.")
print("Cascade depth GROWS / many deep => power-clusters nest => MW wall at every scale => salvage DEAD.")
