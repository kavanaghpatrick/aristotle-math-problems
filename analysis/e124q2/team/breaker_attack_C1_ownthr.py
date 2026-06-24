import numpy as np
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def smaller_atom_rep(D,k,N,bound):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    for a in atoms_list(D,k,N):
        if a>=bound: break
        rep[a:]|=rep[:N+1-a].copy()
    return rep
# ANGLE 3 (the real kill): "smaller-atom reach cofinite up to a" — carry's induction base hypothesis.
# For each atom a, the smaller-atom set (atoms < a) has its OWN threshold own_thr(a). The induction
# needs: residual (n-a) < a is representable by atoms<a. This is fine IF own_thr(a) < a (smaller set
# covers [own_thr(a), a)). carry saw own_thr=a (gap right AT a) for a=64,243. Question: does own_thr(a)
# stay BELOW a (induction ok) or does own_thr(a) -> a (or exceed, leaving (n-a) possibly unreachable)
# for infinitely many a? Compute own_thr(a)/a across atoms a.
print("=== ANGLE 3: own_thr(a) / a across atoms a (induction base: need own_thr(a) < a, ideally <<a) ===")
for D,k in [((3,4,7),1),((3,4,5),2),((3,4,7),2)]:
    print(f" D={D} k={k}:")
    N=20_000_000
    atoms=atoms_list(D,k,N)
    for a in atoms:
        if a<27: continue
        sm=smaller_atom_rep(D,k,a,a)  # smaller-atom set up to a
        exc=np.flatnonzero(~sm[:a])
        own_thr=int(exc[-1]) if len(exc) else 0
        ratio=own_thr/a
        flag=" <-- own_thr/a high (>0.9): induction fragile" if ratio>0.9 else ""
        if a<=atoms[8] or ratio>0.9:  # show small ones + any fragile
            print(f"   a={a}: own_thr(<a)={own_thr}, own_thr/a={ratio:.3f}{flag}")
print("\nKILL angle3 if own_thr(a)/a -> 1 for infinitely many a (smaller set has a gap right below a =>")
print("residual (n-a) in [own_thr(a), a) is UNreachable by atoms<a => valid peel must use a LARGER atom =>")
print("skip-depth grows OR circular reliance on full set). If own_thr(a)/a stays bounded < 1, induction ok.")
