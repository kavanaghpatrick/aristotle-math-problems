import numpy as np
from fractions import Fraction
def repcount(D,k,N):
    ways=np.zeros(N+1,dtype=np.float64); ways[0]=1
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for a in atoms: ways[a:]+=ways[:N+1-a]
    return ways
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def deficit(D): return float(sum(Fraction(1,d-1) for d in D))-1
# D3's specific PREDICTION: log(min-reps below 3^m) ~ m*deficit*const, hits min-reps=1 (gap onset) at
# computable m. Test (3,6,7) deficit=-0.133: D3 predicts gap-onset near 3^16. ACTUAL gap-onset?
# (3,6,7) is reachable: 3^16 = 43M. Compute its actual largest miss.
print("=== D3 PREDICTION CHECK: does deficit-extrapolated gap-onset match ACTUAL gap-onset? ===")
for D,k in [((3,6,7),1),((3,4,7),1)]:
    df=deficit(D)
    # min-reps just below 3^m for m=7..11
    N=50_000_000
    rc=repcount(D,k,N)
    mr=[]
    for m in range(7,12):
        q=3**m
        if q>N: break
        w=rc[max(0,q-500):q]
        mr.append((m,int(w.min())))
    # fit log(min-reps) vs m; extrapolate to min-reps=1
    ms=np.array([m for m,v in mr if v>0],dtype=float)
    lv=np.array([np.log(v) for m,v in mr if v>0])
    if len(ms)>=2:
        slope,intercept=np.polyfit(ms,lv,1)
        m_predict=-intercept/slope if slope<0 else float('inf')  # where log(minreps)=0
    else: slope=float('nan'); m_predict=float('nan')
    # actual gap onset
    exc=np.flatnonzero(~atoms_repset(D,k,N))
    actual_max=int(exc[-1]) if len(exc) else 0
    actual_m = np.log(actual_max)/np.log(3) if actual_max>0 else 0
    print(f"  {D} deficit={df:+.3f}: min-reps below 3^m = {mr}")
    print(f"     fitted slope={slope:.3f} (D3 predicts slope ~ deficit*const); D3-extrapolated gap-onset m={m_predict:.1f}")
    print(f"     ACTUAL largest miss={actual_max} (~3^{actual_m:.1f})")
    print(f"     => min-reps is GROWING (slope>0) so D3 predicts NO gap (m=inf), but actual gap is at 3^{actual_m:.1f}" if slope>0 else "")
