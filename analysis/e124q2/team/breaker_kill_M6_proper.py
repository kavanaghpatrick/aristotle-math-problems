import numpy as np
def Sd1_vals(d,k,N):
    """d^k*B_d values up to N (sums of distinct d^j, j>=k), as a set."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N: p=d**j; rep[p:]|=rep[:N+1-p].copy(); j+=1
    return set(int(x) for x in np.flatnonzero(rep))
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def popcount_base(x,d):
    """number of nonzero digits if x has only 0/1 digits base d, else None."""
    c=0
    while x>0:
        r=x%d
        if r>1: return None
        c+=r; x//=d
    return c
# PROPER M6: rho4(n) = MIN over (a3 in S(3,k), a7 in S(7,k)) of popcount4(n - a3 - a7), minimized over
# all valid splits where n-a3-a7 is a clean 0/1 base-4 number. I.e. the min # base-4 atoms in ANY
# representation. Equivalently: over all reps of n, the minimal count of base-4 atoms used.
def rho4(n,D,k,N,S3,S7,S4set):
    best=99
    for a3 in S3:
        if a3>n: continue
        rem3=n-a3
        for a7 in S7:
            if a7>rem3: continue
            r=rem3-a7
            if r in S4set:
                pc=popcount_base(r,4)  # r is 0/1 base-4 (in S4set), count its atoms
                if pc is not None and pc<best: best=pc
        # early exit if best==0
    return best
print("=== PROPER INV-M6: rho_4(n) = min #base-4 atoms over all reps of n. BOUNDED over rep n? ===")
for D,k,N in [((3,4,7),1,300000),((3,4,7),2,2000000)]:
    full=atoms_repset(D,k,N)
    S3=sorted(Sd1_vals(3,k,N)); S7=sorted(Sd1_vals(7,k,N)); S4set=Sd1_vals(4,k,N)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+3000,N)  # smaller window (the triple loop is O(|S3||S7|))
    maxr=0; vals=[]
    for n in range(lo,hi):
        if not full[n]: continue
        r=rho4(n,D,k,N,S3,S7,S4set)
        if r<99: maxr=max(maxr,r); vals.append(r)
    import numpy as _np
    print(f"  {D} k={k}: window[{lo},{hi}] max rho_4={maxr}, mean={_np.mean(vals):.2f} over {len(vals)} rep n")
print("\nBOUNDED & small (<=6) & k-independent => M6 finite-local repair, real attempt. Grows with n/k => MW => dead.")
