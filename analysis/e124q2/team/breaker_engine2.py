# Faster exact engine using numpy boolean convolution-by-OR via cumulative approach.
import numpy as np

def per_base_bool(d,k,N):
    """boolean array length N+1, True at representable x (sum distinct d^j, j>=k)."""
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    j=k
    while d**j<=N:
        p=d**j
        # rep |= shift(rep, p): rep[p:] |= rep[:N+1-p]
        rep[p:]|=rep[:N+1-p]
        j+=1
    return rep

def sumset_bool(a,b,N):
    """boolean sumset: c[n]=OR_{i} a[i]&b[n-i]. Use the SPARSER one's set positions to shift the denser."""
    ia=np.flatnonzero(a); ib=np.flatnonzero(b)
    if len(ia)<=len(ib):
        small=ia; dense=b
    else:
        small=ib; dense=a
    c=np.zeros(N+1,dtype=bool)
    for p in small:
        if p>N: break
        c[p:]|=dense[:N+1-p]
    return c

def exceptional2(D,k,N):
    arrs=[per_base_bool(d,k,N) for d in D]
    rep=arrs[0]
    for a in arrs[1:]:
        rep=sumset_bool(rep,a,N)
    miss=np.flatnonzero(~rep)
    return miss

if __name__=="__main__":
    import time
    # validate against known
    for k in [1,2,3]:
        t=time.time()
        m=exceptional2((3,4,7),k,4000000)
        print(f"(3,4,7) k={k} N=4M #exc={len(m)} max={m[-1] if len(m) else 0} time={time.time()-t:.1f}s")
