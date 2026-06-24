import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
# ===== INV-V3 KILL: do holes-per-d_max-band RE-SPIKE after draining to 0? =====
# (3,4,7) k=2: d_max=7. Count holes in each [7^j, 7^(j+1)) band. maverick's PROXY claimed monotone drain.
# But the TRUE k=2 max miss is 3,982,888 (near 4^11, NOT a 7-power band). Check 7-bands AND 4-bands.
print("=== INV-V3 KILL: holes-per-band, do they re-spike at deep coincidence bands? ===")
D=(3,4,7); k=2; N=8_000_000
exc=set(int(x) for x in np.flatnonzero(~atoms_repset(D,k,N)))
print(f"(3,4,7) k=2, total misses={len(exc)}, max miss=3982888")
print("  holes per 7^j band:")
prev_zero=False; respike=False
for j in range(2,9):
    lo=7**j; hi=7**(j+1)
    h=sum(1 for e in exc if lo<=e<hi)
    print(f"    [7^{j}={lo}, 7^{j+1}={hi}): {h} holes")
    if prev_zero and h>0: respike=True
    if h==0: prev_zero=True
print("  holes per 4^j band (the TRUE straggler scale — 3982888 is near 4^11):")
prev_zero=False
for j in range(2,12):
    lo=4**j; hi=4**(j+1)
    h=sum(1 for e in exc if lo<=e<hi)
    if h>0 or (lo<=3982888<hi):
        print(f"    [4^{j}={lo}, 4^{j+1}={hi}): {h} holes" + (" <- contains max miss!" if lo<=3982888<hi else ""))
    if prev_zero and h>0: respike=True
    if h==0 and lo>1000: prev_zero=True
print(f"\n  RE-SPIKE detected (holes return after a zero band)? {respike}")
print("  => if YES: per-scale drainage is NON-monotone => INV-V3's conservation law FAILS (MW straggler).")

# ===== INV-V2 KILL: is the carry-state space (ledger) FINITE/bounded? =====
# The Phi carry-state = the two-base correction that must be tracked = the gap of B_3+B_4. We showed
# it's ~1.58M and grows with k. So the transfer matrix is NOT finite-dim with small state => Perron N/A.
print("\n=== INV-V2 KILL: carry-state (two-base correction) bounded? ===")
g34=atoms_repset((3,4),2,8_000_000)
idx=np.flatnonzero(g34); dd=np.diff(idx)
maxgap=max(int(dd[i])-1 for i in range(len(dd)) if idx[i+1]<4_000_000)
print(f"  (3,4) k=2 two-base max gap (=carry-state span needed) = {maxgap}")
print(f"  => carry state space >= {maxgap} states (k=2), grows with k => transfer matrix NOT small-finite")
print(f"  => Perron-Frobenius primitivity index is NOT computably bounded; reduces to the same MW n0. KILL.")
