import numpy as np
def Sd1_vals(d,k,N):
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
    c=0
    while x>0:
        r=x%d
        if r>1: return None
        c+=r; x//=d
    return c
def rho4(n,N,S3,S7,S4set):
    best=99
    for a3 in S3:
        if a3>n: break
        rem3=n-a3
        for a7 in S7:
            if a7>rem3: break
            r=rem3-a7
            if r in S4set:
                pc=popcount_base(r,4)
                if pc is not None and pc<best: best=pc; 
                if best==0: return 0
    return best
# k-dependence of rho4_max. Use windows just above n0(k). Sort S3,S7 for early break.
print("=== INV-M6 k-dependence: rho_4 max over rep n, k=1,2,3 ===")
results={}
for k,N,winsize in [(1,300000,3000),(2,2000000,2000),(3,30000000,1200)]:
    D=(3,4,7)
    full=atoms_repset(D,k,N)
    S3=sorted(Sd1_vals(3,k,N)); S7=sorted(Sd1_vals(7,k,N)); S4set=Sd1_vals(4,k,N)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+winsize,N)
    maxr=0
    for n in range(lo,hi):
        if not full[n]: continue
        r=rho4(n,N,S3,S7,S4set)
        if r<99: maxr=max(maxr,r)
    results[k]=maxr
    print(f"  (3,4,7) k={k}: rho_4 max (window {winsize} above n0={n0}) = {maxr}")
print(f"\n  rho_4 max by k: {results}")
print("  If rho_4 max grows ~linearly with k => encodes the k-scaling = MW content => M6 DEAD for uniformity.")
print("  If bounded (plateaus) => finite-local => M6 real attempt.")
