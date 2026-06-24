import numpy as np

def Sd_vals(d, k, N):
    rep = np.zeros(N+1, dtype=bool); rep[0] = True
    j = k
    while d**j <= N:
        p = d**j; rep[p:] |= rep[:N+1-p].copy(); j += 1
    return rep

def base4_atoms_le_R(k, N, R):
    # all 0/1-base-4 numbers <= N with AT MOST R nonzero digits (atoms 4^j, j>=k)
    powers = []
    j = k
    while 4**j <= N:
        powers.append(4**j); j += 1
    # subset sums with <= R terms
    from itertools import combinations
    vals = {0}
    for r in range(1, R+1):
        for combo in combinations(powers, r):
            s = sum(combo)
            if s <= N:
                vals.add(s)
    return sorted(vals)

# THE NON-CIRCULAR TEST: define T_R = S3 + S7 + (base-4 with <= R atoms). This does NOT assume
# representability — it's a constructive set with a BOUNDED base-4 budget. Question: is T_R cofinite,
# and does the required R stay bounded as N grows / k grows? If a FIXED R makes T_R cofinite (matching
# the full T_k threshold), then M6 gives a genuine constructive proof: every large n needs only <= R
# base-4 atoms, an a-priori bound. If R must grow with N, it's circular/MW.

def threshold_of(reach, N):
    miss = np.flatnonzero(~reach)
    return int(miss[-1]) if len(miss) else -1

for D, k, N in [((3,4,7), 1, 200000), ((3,4,7), 2, 4000000)]:
    S3 = Sd_vals(3, k, N); S7 = Sd_vals(7, k, N)
    # full threshold for reference
    full = np.zeros(N+1, dtype=bool); full[0] = True
    for d in D:
        s = Sd_vals(d, k, N)
        idx = np.flatnonzero(s); new = np.zeros(N+1, dtype=bool)
        for a in idx[:1]: pass
    # build full = S3 + S4 + S7
    def minksum(A, B, N):
        out = np.zeros(N+1, dtype=bool)
        ia = np.flatnonzero(A)
        for a in ia:
            out[a:] |= B[:N+1-a]
        return out
    S4full = Sd_vals(4, k, N)
    full = minksum(minksum(S3, S4full, N), S7, N)
    full_th = threshold_of(full, N)
    print(f"D={D} k={k}: full threshold = {full_th}")
    # now T_R for increasing R
    S3idx = np.flatnonzero(S3); S7idx = np.flatnonzero(S7)
    S37 = minksum(S3, S7, N)  # S3 + S7
    for R in [0, 1, 2, 3, 4, 5, 6]:
        b4 = base4_atoms_le_R(k, N, R)
        TR = np.zeros(N+1, dtype=bool)
        for v in b4:
            if v <= N:
                TR[v:] |= S37[:N+1-v]
        th = threshold_of(TR, N)
        match = "== full (R suffices!)" if th == full_th else ""
        print(f"   R={R}: T_R threshold = {th} {match}")
