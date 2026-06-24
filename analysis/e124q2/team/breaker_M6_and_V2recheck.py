import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Bd1_vals(d,k,N):
    return np.flatnonzero(atoms_repset((d,),k,N))
# ===== INV-M6: rho_4(n) = min #nonzero base-4 (4^{>=k}) digits to represent deficit n - best base-3 part.
def rho4(n,D,k,N,B3set,B4_list):
    # greedy best base-3 part <= n (largest 3^k*B_3 value <= n), deficit = n - that, repaired by base 4(+7)
    # simplify to the (3,4) sub-question per M6: best base-3 part, then min base-4 atoms for deficit (allow +7s too)
    b3=[v for v in B3set if v<=n]
    if not b3: return None
    best3=max(b3)
    deficit=n-best3
    # min # base-4 atoms summing to <=deficit and making (deficit - that) representable by base 7... 
    # M6 core: just count base-4 atoms (0/1) needed to cover deficit. rho4 = popcount-like.
    # use DP: min atoms to reach exactly 'deficit' using distinct 4^j and 7^j
    # cheap proxy: min nonzero base-4 digits in deficit's base-4 rep with digits 0/1 (if rep exists)
    x=deficit; cnt=0
    while x>0:
        if x%4>1: return 99  # uncarriable base-4 digit >=2 => obstruction
        cnt+=x%4; x//=4
    return cnt
print("=== INV-M6: is rho_4 (base-4 repair index) BOUNDED over representable n? ===")
for D,k,N in [((3,4,7),1,2_000_000),((3,4,7),2,8_000_000)]:
    full=atoms_repset(D,k,N); fullset=full
    B3=set(int(x) for x in Bd1_vals(3,k,N))
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+20000,N)
    maxr=0; vals=[]
    for n in range(lo,hi):
        if not fullset[n]: continue
        r=rho4(n,D,k,N,B3,None)
        if r is not None and r<99: maxr=max(maxr,r); vals.append(r)
    print(f"  {D} k={k}: max rho_4 over rep n in [{lo},{hi}] = {maxr} (mean {np.mean(vals):.2f})")
# ===== V2 recheck: carry-state count = # distinct residues mod d_min^s that have a miss, growth with s =====
print("\n=== V2 recheck: # residues mod 3^s with a miss (transfer-matrix state-count proxy) ===")
for D,k,N in [((3,4,7),1,2_000_000),((3,4,7),2,12_000_000)]:
    exc=np.flatnonzero(~atoms_repset(D,k,N))
    print(f"  {D} k={k}:", end=" ")
    for s in range(1,9):
        m=3**s
        live=len(set(int(e)%m for e in exc))
        print(f"s{s}:{live}", end=" ")
    print()
