import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def smaller_atom_repset(D,k,N,bound):
    """representable values using ONLY atoms < bound (the NON-CIRCULAR smaller-atom set)."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for a in atoms_list(D,k,N):
        if a>=bound: break
        rep[a:]|=rep[:N+1-a].copy()
    return rep

# THE NON-CIRCULAR KILL: INV-C1's invariant requires: for rep n>n0, EXISTS atom a<=n with a>=rho*n AND
# (n-a) representable by atoms STRICTLY < a. The non-circular version uses smaller_atom_repset (atoms<a)
# NOT the full set. Test: does this hold? AND is the recursion well-founded (residual rep by SAME structure)?
# Decisive: peel a = largest atom <= n; require (n-a) in repset(atoms < a). If that FAILS for some rep n,
# the valid peel needed a LARGER atom in the residual = NON-contracting / circular. Find such n.
print("=== INV-C1 NON-CIRCULAR kill: peel a>=rho n with (n-a) repr by atoms STRICTLY < a ===")
for D,k,N in [((3,4,7),1,3_000_000),((3,4,5),2,8_000_000),((3,4,5),3,12_000_000)]:
    full=atoms_repset(D,k,N); excf=np.flatnonzero(~full); n0=int(excf[-1]) if len(excf) else 0
    fullset=set(int(x) for x in np.flatnonzero(full))
    allatoms=atoms_list(D,k,N)
    lo=n0+1; hi=min(lo+20000,N)
    fails=0; worst_ratio=0; circular=0
    for n in range(lo,hi):
        if n not in fullset: continue
        ok=False; best_a=0
        for a in reversed([x for x in allatoms if x<=n]):
            # residual must be representable by atoms STRICTLY < a (non-circular, well-founded)
            sm=smaller_atom_repset(D,k,n,a)  # expensive; only when needed
            if (n-a)<=N and sm[n-a]:
                ok=True; best_a=a; break
        if not ok: fails+=1
        else: worst_ratio=max(worst_ratio,(n-best_a)/n if n else 0)
    print(f"  {D} k={k}: window[{lo},{hi}] NON-CIRCULAR valid-peel failures={fails} worst(n-a)/n={worst_ratio:.3f}")
