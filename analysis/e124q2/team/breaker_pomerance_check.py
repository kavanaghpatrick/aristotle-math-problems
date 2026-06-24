import numpy as np
from fractions import Fraction
def repset_atomsieve(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms: rep[p:]|=rep[:N+1-p].copy()
    return rep
def info(D,N):
    exc=np.flatnonzero(~repset_atomsieve(D,0,N))
    b=sum(Fraction(1,d-1) for d in D)
    return float(b), len(exc), (int(exc[-1]) if len(exc) else 0)
# Is B_3+B_4 alone cofinite? beta=1/2+1/3=0.833
print("Testing which subsets are cofinite at k=0, vs their beta:")
for D in [(3,4),(3,11),(4,11),(3,4,11),(3,4,7),(3,4,5)]:
    b,c,m=info(D,100_000_000)
    print(f"  {str(D):<12} beta={b:.4f}  k=0: misses={c} max={m}  {'COFINITE' if m<50_000_000 and c<1000 else 'NOT cofinite' if c>10000 else 'borderline'}")
# CRUX: the Pomerance converse in Lean requires only all d>=3. (3,4,11) all>=3, beta<1, but cofinite.
# Either converse false, or B_3+B_4+B_11 cofiniteness is real and converse is mis-stated.
# Check: is it that 11 = a value already in B_3+B_4 closure making the sum trivially full?
# B_3+B_4 misses up to 1e8:
exc34=np.flatnonzero(~repset_atomsieve((3,4),0,2_000_000))
print(f"\n(3,4) k=0 misses up to 2M: {len(exc34)} (e.g. {exc34[:10].tolist()}) -- so B_3+B_4 NOT cofinite alone")
print("=> adding B_11 (a SPARSE set, density->0) makes it cofinite?? That's the surprising part.")
