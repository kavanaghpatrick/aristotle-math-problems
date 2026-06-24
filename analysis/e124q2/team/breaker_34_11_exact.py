import numpy as np
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def repset(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return rep
D=(3,4,11)
# Exact: full exceptional set for k=0 AND k=1 up to N. Report max miss + count in upper half +
# misses just below each 3^m and 11^m in range.
for k in [0,1]:
    N=400_000_000  # covers 3^17=129M, 3^18=387M
    rep=repset(D,k,N)
    exc=np.flatnonzero(~rep)
    cnt=len(exc); mx=int(exc[-1]) if cnt else 0
    upper=int(np.sum(exc>N//2))
    # misses in [3^m - 3^(m-1), 3^m) for m with 3^m<=N
    bands3=[]
    for m in range(10,18):
        q=3**m
        if q>N: break
        lo=q-3**(m-1)
        b=int(np.sum((exc>=lo)&(exc<q)))
        if b: bands3.append((m,b))
    print(f"k={k} N={N}: count={cnt} max_miss={mx} upper_half_misses={upper} | misses in 3^m bands(m,count)={bands3}", flush=True)
