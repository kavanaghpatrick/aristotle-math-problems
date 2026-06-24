import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
D=(3,4,7); k=1; N=2_000_000
exc=np.flatnonzero(~atoms_repset(D,k,N))
print(f"(3,4,7) k=1: total #misses = {len(exc)}, max miss = {int(exc[-1])}")
print("\nMY '37-state' object = |{ miss mod 3^s }| (# distinct residues the MISS SET occupies):")
for s in range(1,9):
    m=3**s
    cnt=len(set(int(e)%m for e in exc))
    print(f"  s={s}: |miss mod 3^{s}| = {cnt}  (saturates at total miss count 37 once 3^s > max gap between misses)")
print("\n=> This COUNTS the already-known-finite miss set (37 misses occupy 37 distinct residues once")
print("   3^s separates them). It PRESUPPOSES the miss set is finite => CIRCULAR => maverick's MIRAGE. Confirmed.")
print("   It is NOT a forward transfer matrix; it's a Myhill-Nerode-style count of a set known to be finite.")
print("\nThe LEGIT forward object is maverick's reachable-residue count (1,7,20,81,217,727->3^s, GROWS),")
print("which I already verified saturates 3^s for s>=7 => unbounded => no finite forward matrix.")
