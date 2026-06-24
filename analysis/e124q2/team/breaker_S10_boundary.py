import numpy as np
def normalized_logmag(D,k,N,theta):
    logmag=np.zeros_like(theta); mtot=0
    for d in D:
        j=k
        while d**j<=N:
            logmag+=np.log(np.abs(np.cos(np.pi*(d**j)*theta))+1e-18); mtot+=1; j+=1
    return logmag/np.log(2), mtot
# Does the minor-arc decay rate c survive (i) raising k, (ii) at the boundary, AND is c large enough?
# Critical: the major-arc main term must BEAT 2^{mtot(1-c)}. Main term ~ r-average ~ 2^{mtot}/N-ish.
# The bound works iff minor-arc total integral < major main term. Rough check: minor max per-atom c
# vs the "budget". Just confirm c stays bounded-below across k.
print("=== S10 boundary/k-robustness: minor-arc per-atom decay rate c across k ===")
for D in [(3,4,7),(3,5,7,13)]:  # both boundary ∑=1
    print(f" D={D} (∑1/(d-1)=1):")
    for k in [1,2,3]:
        N=min(20_000_000, 5000*max(D)**k)
        ng=2_000_000
        theta=(np.arange(ng)+0.5)/ng
        lg,mtot=normalized_logmag(D,k,N,theta)
        minor=(theta>0.02)&(theta<0.98)
        if mtot==0: continue
        c=-lg[minor].max()/mtot
        print(f"   k={k}: #atoms={mtot}, minor-arc per-atom decay c={c:.4f} (>0 => bound holds)")
# also a strict-excess family for contrast
print(" D=(3,4,5,7) (strict ∑>1):")
for k in [1,2]:
    N=min(20_000_000,5000*7**k); ng=2_000_000; theta=(np.arange(ng)+0.5)/ng
    lg,mtot=normalized_logmag((3,4,5,7),k,N,theta); minor=(theta>0.02)&(theta<0.98)
    c=-lg[minor].max()/mtot
    print(f"   k={k}: #atoms={mtot}, c={c:.4f}")
print("\nIf c stays bounded below >0 across k and families: the decorrelation/minor-arc decay is k-uniform")
print("=> S10 ASYMPTOTIC bound is a real live target (NOT MW-blocked at the harmonic-analysis level).")
