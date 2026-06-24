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
def maxgap_and_bridge(rep):
    idx=np.flatnonzero(rep)
    dd=np.diff(idx)
    maxgap=int(dd.max())-1 if len(dd) else 0
    padded=np.concatenate(([0],rep.view(np.int8),[0]))
    df=np.diff(padded)
    bl=np.flatnonzero(df==-1)-np.flatnonzero(df==1)
    return maxgap, int(bl.max())
def beta(D): return float(sum(Fraction(1,d-1) for d in D))

print("## SUMSET bridge growth — how adding bases builds thickness (the Astels mechanism) ##")
print("Key: single B_d has max-bridge 2. The sumset's max-bridge -> infinity (interval) iff cofinite.\n")
print(f"{'D (cumulative)':<22}{'beta':>8}{'max_gap':>12}{'max_bridge':>12}{'cofinite?':>11}")
# Build up (3,4,7) base by base, and contrast with sub-threshold (3,4,11)
for D in [(3,),(3,4),(3,4,7)]:
    N=10_000_000
    rep=repset_atoms(D,0,N)
    mg,mb=maxgap_and_bridge(rep)
    cof = mg < 1000
    print(f"{str(D):<22}{beta(D):>8.4f}{mg:>12}{mb:>12}{'YES' if cof else 'no':>11}")
print("  --- contrast: sub-threshold path to (3,4,11) ---")
for D in [(3,4),(3,4,11)]:
    N=10_000_000
    rep=repset_atoms(D,0,N)
    mg,mb=maxgap_and_bridge(rep)
    print(f"{str(D):<22}{beta(D):>8.4f}{mg:>12}{mb:>12}{'(deep trap)' if D==(3,4,11) else '':>11}")
print("\n## The critical observation for a discrete thickness definition ##")
print("(3,4,11) beta=0.933<1 has max_bridge LARGE at 10M (looks cofinite) but is NOT (exception>9e9).")
print("=> a correct discrete-thickness invariant must DISTINGUISH (3,4,11) from admissible families")
print("   using FINITE local data, not the global max-bridge (which is fooled by the deep trap).")
