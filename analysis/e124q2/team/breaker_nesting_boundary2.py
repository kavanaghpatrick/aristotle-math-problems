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
def chain_high_theta(n,k,N,full,allatoms,thr=0.8):
    rem=n; cnt=0; guard=0
    while rem>0 and guard<400:
        guard+=1; placed=False
        for a in reversed([x for x in allatoms if x<=rem]):
            if full[rem-a]:
                if a/rem>thr: cnt+=1
                rem-=a; placed=True; break
        if not placed: return cnt,False
    return cnt,True
# (3,4,7) k=3, ABOVE the true threshold 166,025,260. Use N=200M, window just above 166M.
D=(3,4,7); k=3; N=200_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
lo=n0+1; hi=min(lo+8000,N)
maxchain=0; nhigh=0; hist={}
for n in range(lo,hi):
    if not full[n]: continue
    c,ok=chain_high_theta(n,k,N,full,allatoms)
    if c>0: nhigh+=1
    maxchain=max(maxchain,c); hist[c]=hist.get(c,0)+1
print(f"(3,4,7) k=3 BOUNDARY ∑=1, ABOVE threshold (n0={n0}), window[{lo},{hi}]:")
print(f"  MAX high-θ chain levels = {maxchain}, #n with any high-θ = {nhigh}, histogram={dict(sorted(hist.items()))}")
print("  => single-scale (O(1)) obstruction confirmed at boundary high-k" if maxchain<=4 else "  => CASCADE - kill")
