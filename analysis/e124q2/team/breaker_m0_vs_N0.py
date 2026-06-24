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
# cassels' unification: gap-condition onset m0 (first point where +M-closure / no-more-gaps STARTS)
# vs true threshold N0 (last miss). For boundary/sub-threshold families m0 << N0 (gaps persist past m0)
# = my "interval illusion" (looks cofinite at moderate N but isn't / is much deeper).
# Measure: m0 ~ first n after which the LOCAL gap density drops sharply; N0 = last miss.
def stats(D,k,N):
    exc=np.flatnonzero(~repset_atoms(D,k,N))
    if len(exc)==0: return 0,0,0
    N0=int(exc[-1]); cnt=len(exc)
    # m0 proxy: 90th percentile gap position is far below N0 when gaps persist sparsely
    p50=int(np.percentile(exc,50)); p90=int(np.percentile(exc,90))
    return N0, p50, p90
print("cassels unification check: m0 (bulk of misses) vs N0 (last miss). m0<<N0 = illusion/persistent-sparse-gaps")
print(f"{'D':<14}{'k':>2}{'N0(last)':>12}{'p50':>10}{'p90':>11}{'p90/N0':>9}")
for D,k in [((3,4,7),2),((3,4,7),3),((3,5,7,9),3),((3,4,11),1)]:
    N = 300_000_000 if (D==(3,4,11) or k==3) else 8_000_000
    N0,p50,p90=stats(D,k,N)
    r = p90/N0 if N0 else 0
    print(f"{str(D):<14}{k:>2}{N0:>12}{p50:>10}{p90:>11}{r:>9.3f}")
print("\np90/N0 << 1 => 90% of misses are far below the last miss => sparse deep stragglers (the illusion/m0<<N0).")
