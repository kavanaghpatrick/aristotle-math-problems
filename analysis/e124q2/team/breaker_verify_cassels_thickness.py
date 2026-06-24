import numpy as np
def repset_atoms(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def Sd1(d,N):
    """0/1-digit base d, lowest digit 0 (k=1): sums of distinct d^j, j>=1."""
    vals=[0]; j=1
    while d**j<=N: 
        p=d**j; vals=vals+[v+p for v in vals if v+p<=N]; j+=1
    return sorted(vals)

# CLAIM 1: τ_d=1/(d-1) is exact 2-set threshold: B_a+B_b (k=0) cofinite <=> 1/(a-1)+1/(b-1)>=1
from fractions import Fraction
print("CLAIM 1 — 2-set threshold τ_a+τ_b>=1 (k=0):")
pairs=[(2,3),(2,5),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5)]
for a,b in pairs:
    thr=float(Fraction(1,a-1)+Fraction(1,b-1))
    exc=np.flatnonzero(~repset_atoms((a,b),0,5_000_000))
    cof = len(exc)<1000 and (int(exc[-1])<2_500_000 if len(exc) else True)
    print(f"  ({a},{b}) τ-sum={thr:.4f}  cofinite={cof}  (pred cof={thr>=1})  MATCH={cof==(thr>=1)}")

# CLAIM 2: 581-dodge for (3,4,7) k=1. P=3B_3+4B_4 (k=1). Q-elts below 581 = {0,7,49,56,343,350,392,399}
print("\nCLAIM 2 — 581 dodge (3,4,7) k=1:")
N=2000
P=set()
S3=Sd1(3,N); S4=Sd1(4,N)
for a in S3:
    for b in S4:
        if a+b<=N: P.add(a+b)
S7=Sd1(7,581)
print(f"  Q=7·B_7 elements <=581 (k=1): {sorted(S7)}")
rem=[581-e for e in sorted(S7)]
print(f"  581 - Q = {rem}")
print(f"  each in P? {[r in P for r in rem]}")
print(f"  581 dodges all => 581 NOT in P+Q: {all(r not in P for r in rem)}")
# confirm 581 is the largest miss of (3,4,7) k=1
exc347=np.flatnonzero(~repset_atoms((3,4,7),1,2_000_000))
print(f"  largest miss of (3,4,7) k=1 = {int(exc347[-1])} (expect 581)")

# CLAIM 3: (3,4) k=1 max gap and max contiguous run
print("\nCLAIM 3 — (3,4) k=1 gap/run structure:")
rep34=repset_atoms((3,4),1,3_000_000)
idx=np.flatnonzero(rep34); dd=np.diff(idx); maxgap=int(dd.max())-1
padded=np.concatenate(([0],rep34.view(np.int8),[0])); df=np.diff(padded)
runs=np.flatnonzero(df==-1)-np.flatnonzero(df==1); maxrun=int(runs.max())
print(f"  (3,4) k=1: max_gap={maxgap} (cassels says 7682)  max_contiguous_run={maxrun} (cassels says 5137)")
