import numpy as np
def per_base_bool(d,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j; rep[p:]|=rep[:N+1-p]; j+=1
    return rep
def exceptional2(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]; rep=arrs[0]
    for a in arrs[1:]:
        ia=np.flatnonzero(rep); ib=np.flatnonzero(a)
        small,dense=(ia,a) if len(ia)<=len(ib) else (ib,rep)
        c=np.zeros(N+1,dtype=bool)
        for p in small:
            if p>N: break
            c[p:]|=dense[:N+1-p]
        rep=c
    return np.flatnonzero(~rep)
def strict_n0(D,k,Nmax=2_000_000_000):
    hist=[];N=2_000_000
    while N<=Nmax:
        exc=exceptional2(D,k,N); cnt=len(exc); mx=int(exc[-1]) if cnt else 0
        hist.append((cnt,mx,N))
        if len(hist)>=3 and hist[-1][0]==hist[-2][0]==hist[-3][0] and hist[-2][1]<hist[-2][2]//2 and hist[-1][1]<hist[-1][2]//2:
            return mx, N
        N*=2
    return None, Nmax
# carry's claimed thresholds
claims=[((3,4,5),1,79),((3,5,6,7),1,29),((3,5,6,7),2,2318),((3,4,8,12),1,150),((3,4,7),1,581)]
print("Verifying carry's thresholds (strict 2-doubling):")
for D,k,claimed in claims:
    n0,N=strict_n0(D,k)
    ok = (n0==claimed)
    print(f"  {str(D):<14} k={k}: carry={claimed:<8} mine={n0}  {'MATCH' if ok else 'DIFFER'} (verified@N={N})")
