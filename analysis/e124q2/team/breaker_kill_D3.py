import numpy as np
def repcount(D,k,N):
    """number of representations of each n<=N as subset-sum of distinct atoms {d^j,j>=k}.
    DP: ways[n] = number of subsets of atoms summing to n (each atom once)."""
    ways=np.zeros(N+1,dtype=np.int64); ways[0]=1
    atoms=[]
    for d in D:
        j=k
        while d**j<=N: atoms.append(d**j); j+=1
    for a in atoms:
        ways[a:]+=ways[:N+1-a]  # 0/1 knapsack count (each atom once)
    return ways
def min_reps_below(D,k,m,width,N):
    """min repcount over [d_min^m - width, d_min^m)."""
    dmin=min(D); q=dmin**m
    lo=max(0,q-width); hi=min(q,N+1)
    w=repcount(D,k,N)[lo:hi]
    return int(w.min()) if len(w) else None
from fractions import Fraction
def deficit(D): return float(sum(Fraction(1,d-1) for d in D))-1
# INV-D3 decisive: does min-reps just below d_min^m grow/decay with exponent = harmonic deficit?
# For cofinite (deficit>=0): min-reps GROWS (~d_min^{m*deficit}). For gappy (deficit<0): DECAYS to 1 (gap).
print("=== INV-D3 KILL: min-reps below 3^m, fit exponent vs harmonic deficit ===")
for D,k in [((3,4,7),1),((3,4,5),1),((3,5,7),1),((3,6,7),1),((3,5),1),((3,4,11),1)]:
    dmin=min(D); df=deficit(D)
    N=min(60_000_000, dmin**11)
    mr=[]
    for m in range(6,12):
        if dmin**m>N: break
        v=min_reps_below(D,k,m,2000,N)
        mr.append((m,v))
    # fit log(min-reps) vs m*log(dmin): slope ~ deficit?
    ms=np.array([m for m,v in mr if v and v>0],dtype=float)
    lv=np.array([np.log(v) for m,v in mr if v and v>0])
    if len(ms)>=3:
        slope=np.polyfit(ms*np.log(dmin), lv, 1)[0]  # d log(minreps)/d log(d_min^m)
    else: slope=float('nan')
    print(f"  {str(D):<10} deficit={df:+.3f}: min-reps={[(m,v) for m,v in mr]}  fitted exponent={slope:+.3f}")
print("\nKILL if fitted exponent != deficit (D3's predictive claim false). SURVIVE if exponent≈deficit.")
