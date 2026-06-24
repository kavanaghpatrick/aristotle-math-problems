import numpy as np
def repset_atomsieve(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for p in atoms:
        rep[p:]|=rep[:N+1-p].copy()
    return rep
def maxmiss(D,k,N):
    exc=np.flatnonzero(~repset_atomsieve(D,k,N)); return (len(exc), int(exc[-1]) if len(exc) else 0)
# Validation 1: (3,4,7) k=2 must give max 3982888
print("(3,4,7) k=2 N=8M:", maxmiss((3,4,7),2,8_000_000), "(expect count 5207, max 3982888)")
# Validation 2: (3,4) k=0, beta=0.833<1, must be NON-cofinite (misses grow)
for N in [1_000_000, 10_000_000, 100_000_000]:
    c,m=maxmiss((3,4),0,N)
    print(f"(3,4) k=0 N={N}: count={c} max_miss={m} (beta=0.833, should be NON-cofinite => max~N)")
# Validation 3: (3,4,11) k=0 — is it REALLY cofinite? cross-check with the OLD slow engine on small N
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def repset_old(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep)
        c=np.zeros(N+1,dtype=bool)
        for p in ia:
            if p>N: break
            c[p:]|=a[:N+1-p]
        rep=c
    return rep
N=2_000_000
old=np.flatnonzero(~repset_old((3,4,11),0,N))
new=np.flatnonzero(~repset_atomsieve((3,4,11),0,N))
print(f"(3,4,11) k=0 N={N}: old_engine misses={len(old)}, atom_sieve misses={len(new)}, MATCH={set(old.tolist())==set(new.tolist())}")
