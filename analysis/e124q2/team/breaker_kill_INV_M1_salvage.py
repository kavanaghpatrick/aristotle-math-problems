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
# SALVAGE TEST: take a representable n, peel the largest atom a<=n with (n-a) representable;
# recurse on r=n-a. Track theta=a/n at EACH level. Question: does the recursion CASCADE through
# theta->1 (high-theta) points at every scale, or do the theta values stay bounded after a few steps?
# If max theta over the recursion chain stays <1-eps for MOST n (cascade terminates), salvage works.
def recursion_thetas(n, D, k, N, full, allatoms):
    thetas=[]; rem=n; guard=0
    while rem>0 and guard<300:
        guard+=1
        placed=False
        for a in reversed([x for x in allatoms if x<=rem]):
            if (rem-a)>=0 and (rem-a)<=N and full[rem-a]:
                thetas.append(a/rem); rem-=a; placed=True; break
        if not placed: return thetas, False  # stuck
    return thetas, True
print("=== INV-M1/C1 SALVAGE: does the peel-recursion cascade through θ→1 at every scale? ===")
for D,k,N in [((3,4,5),2,8_000_000),((3,4,5),3,12_000_000),((3,5,7,9),2,8_000_000)]:
    full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    fullset=full
    lo=n0+1; hi=min(lo+5000,N)
    # for each rep n, the MAX theta over its FULL recursion chain (not just level 0)
    chain_max_thetas=[]
    high_chain=0  # n whose chain has theta>0.95 at EVERY level (would be the cascade/wall)
    for n in range(lo,hi):
        if not fullset[n]: continue
        th,ok=recursion_thetas(n,D,k,N,fullset,allatoms)
        if th:
            chain_max_thetas.append(max(th))
            # cascade signature: does theta stay >0.9 for many consecutive levels?
            consec=0; mx_consec=0
            for t in th:
                if t>0.9: consec+=1; mx_consec=max(mx_consec,consec)
                else: consec=0
            if mx_consec>=3: high_chain+=1
    cmt=np.array(chain_max_thetas)
    print(f"  {D} k={k}: chain-max-θ: mean={cmt.mean():.3f} p99={np.percentile(cmt,99):.3f} max={cmt.max():.3f}")
    print(f"       #n whose recursion has θ>0.9 for >=3 CONSECUTIVE levels (cascade signature): {high_chain}/{len(cmt)}")
print("\nKILL salvage if: many n cascade (θ>0.9 at consecutive recursion levels = MW wall at every scale).")
print("Salvage SURVIVES if: recursion chains drop below θ-threshold within O(1) levels (no deep cascade).")
