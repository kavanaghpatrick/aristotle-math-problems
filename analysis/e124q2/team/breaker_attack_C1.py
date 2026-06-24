import numpy as np
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for p in atoms_list(D,k,N): rep[p:]|=rep[:N+1-p].copy()
    return rep
def smaller_atom_rep(D,k,N,bound):
    """representable by atoms STRICTLY < bound."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for a in atoms_list(D,k,N):
        if a>=bound: break
        rep[a:]|=rep[:N+1-a].copy()
    return rep

# ATTACK ANGLE 1+2: find ANY rep n>N0 with NO valid peel, or contraction ratio rho->1.
# Hit the HARDEST regime: boundary family (3,4,7) k=3 JUST above the TRUE threshold 166M (where the
# high-theta cascade is pervasive — most likely to break INV-C1).
print("=== ATTACK C1 angle 1+2: boundary (3,4,7) k=3 ABOVE true threshold 166M ===")
D=(3,4,7); k=3; N=200_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
lo=n0+1; hi=lo+20000
# NON-CIRCULAR valid peel: largest a<=n with (n-a) representable by atoms STRICTLY < a
# (precompute smaller-atom reps lazily — cache by bound)
cache={}
def smrep(bound):
    if bound not in cache: cache[bound]=smaller_atom_rep(D,k,N,bound)
    return cache[bound]
fails=0; worst_rho=0; worst_n=None
checked=0
for n in range(lo,hi):
    if not full[n]: continue
    checked+=1
    ok=False
    for a in reversed([x for x in allatoms if x<=n]):
        if (n-a)>=0 and smrep(a)[n-a]:
            ok=True
            rho=(n-a)/n  # residual fraction; contraction = peel shrinks n to rho*n
            if rho>worst_rho: worst_rho=rho; worst_n=n
            break
    if not ok: fails+=1
print(f"  (3,4,7) k=3 ABOVE 166M: checked {checked} rep n, NON-CIRCULAR valid-peel FAILURES={fails}")
print(f"  worst residual ratio (n-a)/n = {worst_rho:.4f} at n={worst_n} (contraction = peel to {worst_rho:.2f}n)")
print(f"  => angle 1 {'KILLED C1' if fails>0 else 'C1 survives (peel always exists)'}; angle 2 {'KILLED (rho->1)' if worst_rho>0.95 else f'C1 survives (rho<={worst_rho:.2f}<1, O(log n) depth)'}")
