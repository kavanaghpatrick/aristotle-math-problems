import numpy as np
# INV-S10: uniform minor-arc bound |F_3 F_4 F_7| << N^{3-delta}, delta>0.
# F_d(theta) = prod_{j: d^j<=N} (1 + e(d^j theta)), |1+e(x)| = 2|cos(pi x)|. Trivial max = 2^{#factors}.
# Normalized: |F_d|/2^{#factors_d}. The product's TRIVIAL bound is prod 2^{#factors} ~ N^{log2/log3 + ...}.
# Actually |F_d| <= 2^{m_d}, m_d = #atoms of base d <= N. Total trivial = 2^{m_3+m_4+m_7}.
# The "N^3" in S10 is loose notation; the REAL test (scope-correct, ASYMPTOTIC): does the MINOR-ARC
# max of |F_3 F_4 F_7| / (trivial max) DECAY as N grows (=> delta>0 => bound holds => r(n)>0 for large n)?
def logF_normalized_max_minorarc(D,k,N,ngrid,arc_excl):
    """max over minor arcs (theta away from a/d^j by arc_excl) of |prod F_d| / trivial-max."""
    theta=np.arange(1,ngrid)/ngrid  # exclude theta=0
    logmag=np.zeros(ngrid-1)
    mtot=0
    for d in D:
        j=k
        while d**j<=N:
            logmag+=np.log(np.abs(np.cos(np.pi*(d**j)*theta))+1e-300)
            mtot+=1; j+=1
    # |prod F| = 2^{mtot} * exp(logmag). normalized = exp(logmag) (in [0,1], =1 only at theta where all cos=±1)
    norm=np.exp(logmag)  # this is |prod F|/2^mtot
    # minor arc: exclude theta within arc_excl of any a/d^j (small denom). Approx: exclude near 0 and near
    # rationals with denom <= a few powers. Cheap proxy: exclude |theta - a/d^j| < arc_excl.
    mask=np.ones(ngrid-1,dtype=bool)
    for d in D:
        for j in range(k, k+4):  # small-denom rationals
            for a in range(0,d**j+1):
                c=a/d**j
                mask &= np.abs(theta-c)>arc_excl
    minor=norm[mask]
    return minor.max() if len(minor) else 0, mtot
print("=== INV-S10 SCOPE-CORRECT test: does minor-arc max of |F_3F_4F_7|/trivial DECAY with N? ===")
print("(decay => delta>0 => uniform bound holds => ASYMPTOTIC r(n)>0. No decay => bound fails.)")
D=(3,4,7); k=1
for N in [2000, 20000, 200000, 2000000]:
    ng=1<<18
    mx,mtot=logF_normalized_max_minorarc(D,k,N,ng,0.005)
    # express as exponent: |prod F| ~ 2^mtot * mx = N^{?}. delta indicator: mx vs 1.
    # the bound N^{3-delta} <=> mx <= (trivial)^{-delta/3}-ish; cleanest: track mx and mtot.
    print(f"  N={N:>8}: #atoms={mtot}, minor-arc max normalized |F_3F_4F_7| = {mx:.4e}  (log2-deficit per atom={-np.log2(mx)/mtot if mx>0 else 0:.3f})")
print("\nIf normalized minor-arc max -> 0 (per-atom log2-deficit bounded BELOW by c>0): delta>0, S10 ASYMPTOTIC holds.")
print("If it stays O(1) / per-atom deficit -> 0: no uniform bound, S10 dies even asymptotically.")
