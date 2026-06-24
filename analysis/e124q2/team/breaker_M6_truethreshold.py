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
def rho4(n,S3,S7,S4set):
    best=99
    for a3 in S3:
        if a3>n: break
        rem3=n-a3
        for a7 in S7:
            if a7>rem3: break
            r=rem3-a7
            if r in S4set:
                pc=popcount_base(r,4)
                if pc is not None and pc<best:
                    best=pc
                    if best==0: return 0
    return best
# M6 at the TRUE (3,4,7) k=3 threshold region (166M) where the high-θ cascade is pervasive.
D=(3,4,7); k=3; N=200_000_000
full=atoms_repset(D,k,N)
S3=sorted(Sd1_vals(3,k,N)); S7=sorted(Sd1_vals(7,k,N)); S4set=Sd1_vals(4,k,N)
n0=166025260
lo=n0+1; hi=lo+800
maxr=0; vals=[]
for n in range(lo,hi):
    if not full[n]: continue
    r=rho4(n,S3,S7,S4set)
    if r<99: maxr=max(maxr,r); vals.append(r)
print(f"INV-M6 at TRUE k=3 threshold (3,4,7) n0={n0}, window[{lo},{hi}]:")
print(f"  rho_4 max = {maxr}, mean = {np.mean(vals):.2f} over {len(vals)} rep n")
print(f"  => {'BOUNDED ~6 even at the pervasive-cascade boundary' if maxr<=8 else 'SPIKES at boundary'}")
