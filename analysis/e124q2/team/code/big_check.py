import sys
import numpy as np
# memory-efficient coverage to large N using numpy boolean sieve and FFT-free Minkowski via cumulative OR shifts
def powers(d,k,N):
    ps=[]; j=k
    while d**j<=N: ps.append(d**j); j+=1
    return ps
def reach_np(D,k,N):
    cur=np.zeros(N+1,dtype=bool); cur[0]=True
    for d in D:
        s=np.zeros(N+1,dtype=bool); s[0]=True
        for p in powers(d,k,N):
            s[p:] |= s[:-p] if p<=N else s[:0]
        # minkowski cur (+) s : new[n] = OR_{a: cur[a]} s[n-a]
        # do via: for each power-of-two? Simpler: iterate set bits of the SPARSER one.
        # s (single base) is sparse-ish early but dense later. cur grows dense. Use np.convolve-like via FFT? 
        # Use: new = OR over shifts by indices where the smaller-support array is True.
        idx_cur = np.flatnonzero(cur)
        idx_s = np.flatnonzero(s)
        if len(idx_cur)<=len(idx_s):
            small, big_arr = idx_cur, s
        else:
            small, big_arr = idx_s, cur
        new=np.zeros(N+1,dtype=bool)
        for a in small:
            new[a:] |= big_arr[:N+1-a]
        cur=new
    return cur
if __name__=="__main__":
    D=tuple(int(x) for x in sys.argv[1].split(',')); k=int(sys.argv[2]); N=int(sys.argv[3])
    r=reach_np(D,k,N)
    miss=np.flatnonzero(~r)
    if len(miss)==0:
        print(f"D={D} k={k} N={N}: NO gaps (cofinite to N)")
    else:
        print(f"D={D} k={k} N={N}: largest_missing={int(miss[-1])} count={len(miss)} first_few={miss[:5].tolist()} last_few={miss[-5:].tolist()}")
