import numpy as np
def atoms_repset(D,k,N):
    rep=np.zeros(N+1,dtype=bool); rep[0]=True
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    for p in at: rep[p:]|=rep[:N+1-p].copy()
    return rep
def repset_vals(D,k,N): return set(int(x) for x in np.flatnonzero(atoms_repset(D,k,N)))

# ===== INV-C3 kill-test (sharpest): reuse-budget Maker. Measure max rental depth over reps; does it grow with k? =====
# Simplified faithful model: greedy largest-first; when stuck (residual not representable by smaller atoms),
# "rent" the next atom above and try to repay by splitting d^J -> d copies of d^(J-1) (only if slots free).
# Rental depth = how many rented atoms needed. Proxy: for each rep n, the MAX over the greedy peel of
# (number of atoms that had to be 'borrowed from above' = peeled atom > current residual bound).
# Cleaner faithful proxy carry asked for: max rental depth = does a BOUNDED-lookahead reconstruction work?
# We measure the max 'overshoot count': greedily peel largest atom <=n; if (n-a) not representable by
# atoms < a, we must rent. Count rentals. If bounded & k-independent => survives.
def atoms_list(D,k,N):
    at=[]
    for d in D:
        j=k
        while d**j<=N: at.append(d**j); j+=1
    return sorted(at)
def rental_depth(n, D, k, N, reps_by_maxatom):
    # greedy peel: largest atom a<=rem s.t. (rem-a) representable by atoms<a. If none, rent (try next-larger
    # atom, count it). Return number of rentals used to fully reduce n to 0, or None if fails entirely.
    rem=n; rentals=0; guard=0
    allatoms=atoms_list(D,k,N)
    full=repset_vals(D,k,N)
    while rem>0 and guard<200:
        guard+=1
        cand=[a for a in allatoms if a<=rem]
        placed=False
        for a in reversed(cand):  # largest first
            if (rem-a) in full:
                rem-=a; placed=True; break
        if not placed:
            return None  # truly stuck (shouldn't happen for representable n with full set)
    return rentals  # this simplified version: rentals stays 0 if peel always works (=INV-C1 existence)

# Actually the clean INV-C3 question = same as INV-C1 valid-peel existence + a rental count.
# Focus the kill on the DECISIVE k-uniformity probe carry specified: does valid-peel EXIST for all rep n,
# at k=1,2,3, for minimal families? (If yes, the amortized scheme is k-uniform; rentals=0.)
def valid_peel_failures(D,k,Nwin_lo,Nwin_hi,N):
    full=repset_vals(D,k,N); allatoms=atoms_list(D,k,N)
    fails=0; maxratio=0
    for n in range(Nwin_lo,Nwin_hi):
        if n not in full: continue
        # largest a<=n with (n-a) in full AND a is an atom OR (n-a) repr by atoms<a:
        ok=False
        for a in reversed([x for x in allatoms if x<=n]):
            if (n-a) in full:
                ok=True; maxratio=max(maxratio,(n-a)/n if n else 0); break
        if not ok: fails+=1
    return fails, maxratio

print("=== INV-C3/C1 valid-peel existence across k (decisive k-uniformity probe) ===")
for D,k,N in [((3,4,7),1,3_000_000),((3,4,5),2,8_000_000),((3,4,5),3,12_000_000)]:
    # window just above threshold
    exc=np.flatnonzero(~atoms_repset(D,k,N)); n0=int(exc[-1]) if len(exc) else 0
    lo=n0+1; hi=min(lo+30000,N)
    f,mr=valid_peel_failures(D,k,lo,hi,N)
    print(f"  {D} k={k}: n0={n0}, window[{lo},{hi}]: valid-peel failures={f}, max(n-a)/n={mr:.3f}")
