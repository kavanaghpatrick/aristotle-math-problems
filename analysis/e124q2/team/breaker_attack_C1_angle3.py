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
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for a in atoms_list(D,k,N):
        if a>=bound: break
        rep[a:]|=rep[:N+1-a].copy()
    return rep
# ANGLE 3 (THE CRUX): the NON-CIRCULAR density-envelope version of INV-C1's invariant. carry's claim:
# "reach of atoms <a covers [0,(1-rho)n] for a>=rho*n". If TRUE, the residual (n-a) in [0,(1-rho)n] is
# AUTOMATICALLY representable by smaller atoms (no need for the full set) => non-circular proof.
# KILL if: the smaller-atom set has GAPS in [0,(1-rho)n], so for some n the residual lands in a gap
# and the peel only works by REFERENCE to the full set (circular). 
# Test: for the chosen peel a, is the smaller-atom set CONTIGUOUS up to (n-a)? Or does (n-a) sit just
# past a gap in the smaller-atom set that a coarser argument couldn't predict?
print("=== ATTACK C1 angle 3 (circularity): is the smaller-atom set an INTERVAL up to the residual? ===")
for D,k,N in [((3,4,7),1,3_000_000),((3,4,5),2,8_000_000)]:
    full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
    exc=np.flatnonzero(~full); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+10000,N)
    cache={}
    def smrep(b):
        if b not in cache: cache[b]=smaller_atom_rep(D,k,N,b)
        return cache[b]
    # for each n, find the peel a; check: is smaller-atom set CONTIGUOUS on [0, n-a]? If NOT, the
    # residual being representable is a NON-TRIVIAL fact (smaller set has gaps) => not a clean envelope.
    residual_in_gap_region=0; smaller_has_gaps_below_residual=0; checked=0
    for n in range(lo,hi):
        if not full[n]: continue
        checked+=1
        for a in reversed([x for x in allatoms if x<=n]):
            sm=smrep(a)
            if (n-a)>=0 and sm[n-a]:
                # is sm contiguous on [0, n-a]? i.e. does the smaller-atom set have NO gaps below the residual?
                if not sm[:n-a+1].all():
                    smaller_has_gaps_below_residual+=1
                break
    frac=smaller_has_gaps_below_residual/checked if checked else 0
    print(f"  {D} k={k}: of {checked} rep n, {smaller_has_gaps_below_residual} ({frac:.1%}) have the smaller-atom set")
    print(f"       NON-contiguous below the residual => the peel exploits the smaller set's FINE structure,")
    print(f"       NOT just a density envelope. {'CIRCULARITY CONFIRMED (envelope insufficient)' if frac>0.5 else 'envelope may suffice'}")
