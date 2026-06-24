import numpy as np
# Proper S10 test: the minor-arc magnitude of |F_3 F_4 F_7|. Use a FINE grid and report the max of the
# normalized product OFF a neighborhood of theta=0 (the major arc). Track how the max log2-magnitude
# (as a FRACTION of the trivial 2^mtot) scales. The asymptotic bound needs this fraction -> 0.
def normalized_logmag(D,k,N,theta):
    logmag=np.zeros_like(theta); mtot=0
    for d in D:
        j=k
        while d**j<=N:
            logmag+=np.log(np.abs(np.cos(np.pi*(d**j)*theta))+1e-18); mtot+=1; j+=1
    return logmag/np.log(2), mtot  # log2 of normalized product (<=0)
D=(3,4,7); k=1
print("=== S10 v2: minor-arc max of log2(|F_3F_4F_7|/2^mtot), off major arc |theta|>0.02 ===")
print("(The product is N^{3-delta} iff this max-log2 / mtot is bounded below by a constant >0, i.e.")
print(" the normalized product decays exponentially in #atoms uniformly on minor arcs.)")
for N in [20000, 200000, 2000000, 20000000]:
    # fine grid avoiding exact rationals; sample densely
    ng=2_000_000
    theta=(np.arange(ng)+0.5)/ng
    lg,mtot=normalized_logmag(D,k,N,theta)
    # major arc = within 0.02 of 0 or 1
    minor= (theta>0.02)&(theta<0.98)
    maxlog2=lg[minor].max()  # closest to 0 = largest product on minor arc
    print(f"  N={N:>9}: #atoms(mtot)={mtot}, max log2-normalized on minor arc={maxlog2:.2f}  (per-atom={maxlog2/mtot:.4f})")
print("\nINTERPRET: per-atom log2 = maxlog2/mtot. If it stays <= -c (c>0) as N grows, the product is")
print("<= 2^{mtot(1-c)} = N^{3-delta} with delta>0 (S10 ASYMPTOTIC bound HOLDS). If per-atom -> 0,")
print("some minor-arc point keeps the product near-trivial => NO uniform decay => S10 fails asymptotically too.")
