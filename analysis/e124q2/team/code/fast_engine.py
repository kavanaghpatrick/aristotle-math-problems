# Fast numpy boolean engine for R(D,k) = sum_{d in D} d^k * B_d, recreated (cf breaker).
import numpy as np
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j
        rep[p:]|=rep[:N+1-p]
        j+=1
    return rep
def sumset_bool(a,b,N):
    ia=np.flatnonzero(a); ib=np.flatnonzero(b)
    small=ia if len(ia)<=len(ib) else ib
    dense=b if len(ia)<=len(ib) else a
    c=np.zeros(N+1,dtype=bool)
    for p in small:
        if p>N: break
        c[p:]|=dense[:N+1-p]
    return c
def exceptional(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]
    rep=arrs[0]
    for a in arrs[1:]:
        rep=sumset_bool(rep,a,N)
    return np.flatnonzero(~rep)
