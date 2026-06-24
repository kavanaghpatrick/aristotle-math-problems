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
# ANGLE 1+2 refined: SKIP-DEPTH at the HARDEST regime — boundary (3,4,7) k=3 ABOVE true threshold 166M.
# skip-depth(n) = index (from largest) of the first atom a<=n with (n-a) repr by atoms STRICTLY < a.
# carry claims <=2 k-uniform but only tested k<=2 / non-boundary. Test where the cascade is pervasive.
D=(3,4,7); k=3; N=200_000_000
full=atoms_repset(D,k,N); allatoms=atoms_list(D,k,N)
exc=np.flatnonzero(~full); n0=int(exc[-1])
cache={}
def smrep(b):
    if b not in cache: cache[b]=smaller_atom_rep(D,k,N,b)
    return cache[b]
lo=n0+1; hi=lo+8000
maxskip=0; skipfail=0; hist={}; worst_n=None
for n in range(lo,hi):
    if not full[n]: continue
    cand=[a for a in allatoms if a<=n][::-1]  # largest first
    depth=None
    for i,a in enumerate(cand):
        if (n-a)>=0 and smrep(a)[n-a]:
            depth=i; break
    if depth is None: skipfail+=1
    else:
        maxskip=max(maxskip,depth); hist[depth]=hist.get(depth,0)+1
        if depth>2 and worst_n is None: worst_n=(n,depth)
print(f"(3,4,7) k=3 ABOVE 166M threshold, window[{lo},{hi}]:")
print(f"  skip-depth histogram (depth:count) = {dict(sorted(hist.items()))}")
print(f"  MAX skip-depth = {maxskip}  (carry claims <=2 k-uniform)")
print(f"  skip-FAILURES (no valid peel in any atom) = {skipfail}")
if worst_n: print(f"  first n with skip-depth>2: n={worst_n[0]}, depth={worst_n[1]}")
print(f"  => {'KILL: skip-depth EXCEEDS 2 at boundary k=3' if maxskip>2 else 'skip-depth <=2 holds even at boundary k=3'}")
