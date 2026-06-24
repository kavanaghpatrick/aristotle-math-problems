import numpy as np
# k=0 case: B_d = all 0/1-digit base-d numbers (INCLUDING d^0=1). Test (3,4,11) k=0 cofiniteness.
def per_base_bool_k0(d,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=0
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def exceptional_k0(D,N):
    arrs=[per_base_bool_k0(d,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return np.flatnonzero(~rep)
# k=0: is (3,4,11) cofinite? The converse says cofinite => beta>=1. beta(3,4,11)=0.933<1.
# So converse PREDICTS (3,4,11) k=0 is NOT cofinite (infinitely many misses).
D=(3,4,11)
for N in [10_000_000, 100_000_000, 500_000_000]:
    exc=exceptional_k0(D,N)
    cnt=len(exc); mx=int(exc[-1]) if cnt else 0
    upper=int(np.sum(exc>N//2))
    print(f"k=0 (3,4,11) N={N}: count={cnt} max={mx} upper_half_misses={upper} density_upper={upper/(N//2):.2e}")
