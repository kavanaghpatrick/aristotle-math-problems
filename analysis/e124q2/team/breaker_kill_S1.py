import numpy as np
# INV-S1 multi-base circle method: r(n) = integral_0^1 prod_d F_d(theta) e(-n theta) dtheta,
# F_d(theta) = prod_{j>=k, d^j<=N} (1 + e(d^j theta)). This is exactly the generating function for
# representation count r(n) = #subsets of atoms summing to n. KILL-TEST: at k=1 (KNOWN cofinite),
# is the count dominated by the MAJOR-arc (theta near 0) main term, or do MINOR arcs swamp it?
# We compute r(n) exactly via FFT, then estimate the major-arc contribution (theta in [-1/(2Q),1/(2Q)])
# and compare to the full r(n). If major-arc term alone predicts r(n)>0 for all n>581, S1 viable.
D=(3,4,7); k=1
# atoms
atoms=[]
for d in D:
    j=k
    while d**j<=5000: atoms.append(d**j); j+=1
M=5000
# r(n) exact: coefficient extraction = subset-sum count. Use the circle-method numerically:
# sample theta on a fine grid, compute prod F_d, inverse-FFT to get r(n).
Ngrid=1<<16
theta=np.arange(Ngrid)/Ngrid
F=np.ones(Ngrid,dtype=complex)
for a in atoms:
    F*= (1+np.exp(2j*np.pi*a*theta))
r=np.fft.ifft(F).real  # r[n] ~ representation count (real, should be near-integer)
r=np.round(r).astype(int)
print(f"INV-S1 circle method, (3,4,7) k=1: r(n) via FFT, atoms={atoms[:10]}...")
# verify r(n)=0 exactly at the known misses, >0 above 581
misses=[n for n in range(M) if n<Ngrid and r[n]==0]
print(f"  r(n)=0 at n<{M}: count={len(misses)}, max miss={max([m for m in misses if m>0]) if misses else 0} (expect 581)")
# MAJOR-ARC test: contribution from theta near 0 (the only common major arc, per scholar's decorrelation).
# Major arc width ~ 1/Q. Estimate the major-arc-only count = integral over |theta|<1/(2Q) of prod F.
for Q in [8,16,32]:
    w=Ngrid//(2*Q)
    idx=np.concatenate([np.arange(0,w),np.arange(Ngrid-w,Ngrid)])
    # major-arc reconstruction of r(n) for sample n
    maj=np.zeros(Ngrid,dtype=complex)
    Fmaj=np.zeros(Ngrid,dtype=complex); Fmaj[idx]=F[idx]
    rmaj=np.fft.ifft(Fmaj).real
    # does major-arc term stay positive (track sign) above 581?
    above=rmaj[582:M]
    frac_pos=np.mean(above>0)
    print(f"  Q={Q}: major-arc-only r(n) for n in [582,{M}]: fraction POSITIVE = {frac_pos:.3f}, min={above.min():.1f}")
print("\nKILL if major-arc term is NOT reliably positive above 581 (minor arcs carry the signal => method")
print("can't separate). VIABLE if major-arc alone stays positive (the main term dominates).")
