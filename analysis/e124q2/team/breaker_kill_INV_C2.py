import numpy as np
# INV-C2 kill: carry-ledger automaton. The candidate claims a FINITE-STATE ledger L in [-B,B] suffices.
# Kill if max|L| GROWS with n (unbounded ledger => infinite-state => dead).
# Faithful model: process n by greedily matching residues mod b^k*c^k using the two smallest bases b,c,
# track the "carry ledger" = signed deficit that must be repaid. The honest proxy for L: the minimal
# number of atoms (signed) by which a greedy two-base reduction misses, before other bases correct.
# Cleanest computable proxy carry specified: track max|L| where L = running mismatch in the mixed-radix
# digit reconciliation. We use: for representable n, the MINIMUM over representations of the max partial
# "two-base carry". Approximate by the greedy base-b/base-c digit reconciliation.
# Practical kill metric (what carry asked): does the ledger needed stay bounded? Proxy = max gap that the
# two smallest bases LEAVE for the other bases to fill, as a function of scale. If that 'correction
# magnitude' is bounded & n-independent => finite state. If it grows with n => unbounded ledger.
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def two_base_correction(D,k,N):
    """For each n, min |n - (two-base part)| over the two-smallest-base sumset = the 'ledger/correction'
    the other bases must supply. If this is bounded over all n, finite-state. Measure max over windows."""
    b,c=sorted(D)[:2]
    twobase=np.flatnonzero(atoms_repset((b,c),k,N))  # values from b^k B_b + c^k B_c
    twobase=np.array(sorted(twobase))
    # for n in windows, nearest two-base value below n; correction = n - that (must be supplied by rest)
    # max correction over a window = how big a 'ledger' the rest must absorb
    res={}
    for center in [10000,100000,1000000]:
        if center>N: continue
        lo=center; hi=min(center+5000,N)
        maxcorr=0
        idx=np.searchsorted(twobase, np.arange(lo,hi), side='right')-1
        for ni,n in enumerate(range(lo,hi)):
            below=twobase[idx[ni]] if idx[ni]>=0 else 0
            maxcorr=max(maxcorr, n-below)
        res[center]=maxcorr
    return res, b, c
print("=== INV-C2 kill: does the two-base ledger/correction stay BOUNDED across scale? ===")
for D,k in [((3,4,7),1),((3,4,5),1)]:
    r,b,c=two_base_correction(D,k,8_000_000)
    print(f"  {D} k={k} (two smallest {b},{c}): max two-base correction by scale: {r}")
print("\nKILL if correction GROWS with scale (unbounded ledger => infinite-state automaton => INV-C2 dead).")
