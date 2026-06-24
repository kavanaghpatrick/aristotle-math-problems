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
def chain_high_theta(n,N,full,allatoms,thr=0.8):
    rem=n; cnt=0; guard=0
    while rem>0 and guard<400:
        guard+=1; placed=False
        for a in reversed([x for x in allatoms if x<=rem]):
            if full[rem-a]:
                if a/rem>thr: cnt+=1
                rem-=a; placed=True; break
        if not placed: return cnt,False
    return cnt,True
D=(3,4,7); k=3; N=200_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
# Compare cascade depth at threshold vs WELL ABOVE it (does it thin to single-scale away from n0?)
print("(3,4,7) k=3: high-θ cascade depth at different distances above threshold n0=166M:")
for center,label in [(166_030_000,"just above n0 (+5K)"),(175_000_000,"+9M above n0"),(195_000_000,"+29M above n0")]:
    lo=center; hi=lo+5000
    maxc=0; nhigh=0
    for n in range(lo,hi):
        if not full[n]: continue
        c,ok=chain_high_theta(n,N,full,allatoms)
        if c>0: nhigh+=1
        maxc=max(maxc,c)
    print(f"  {label}: max cascade={maxc}, #high-θ={nhigh}/5000")
print("\nIf cascade THINS away from n0 (single-scale far from threshold) but is dense AT n0, the salvage")
print("works ABOVE a margin but the threshold-region itself is the irreducible MW core (expected).")
