import numpy as np
from fractions import Fraction
def repset_atoms(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def longest_initial_run(rep):
    """length of [0, X] fully representable (the cofinite-from-0 prefix), i.e. first gap position."""
    idx=np.flatnonzero(~rep)
    return int(idx[0]) if len(idx) else len(rep)
def beta(D): return float(sum(Fraction(1,d-1) for d in D))
# Task #15 raw material: as bases added in order, track the largest GAP and the n0 (last miss).
# The Astels claim: when cumulative thickness crosses 1, the sumset becomes an interval (n0 finite/small).
print("Sequential base-addition: largest gap + n0 as cumulative β crosses 1 (k=1, the open case).")
for order in [[3,4,7],[3,4,5],[3,5,7,13],[4,5,6,7,8]]:
    print(f"\n building {order} (k=1):")
    for i in range(1,len(order)+1):
        D=tuple(order[:i])
        N=20_000_000
        rep=repset_atoms(D,1,N)
        exc=np.flatnonzero(~rep)
        n0=int(exc[-1]) if len(exc) else 0
        cnt=len(exc)
        b=beta(D)
        # max gap
        idx=np.flatnonzero(rep); dd=np.diff(idx); mg=int(dd.max())-1 if len(dd) else 0
        status = "INTERVAL(cofinite)" if (cnt< 100000 and n0<N//2) else f"gaps(maxgap={mg})"
        print(f"   {str(D):<16} β={b:.4f}  n0={n0:<10} #miss={cnt:<9} {status}")
