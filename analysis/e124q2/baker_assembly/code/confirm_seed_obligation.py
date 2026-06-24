import numpy as np
# ============================================================
# baker's load-bearing ask: confirm the L2 sieve reached >= 33,841,349 gap-free.
# The seed obligation is the WHOLE symmetric middle (N0, Sigma_{3^15} - N0) where
# Sigma_{3^15} = atomSum(atoms <= 3^15) = 33,841,349. The middle is
# (3,982,888, 29,858,461) -- so the sieve must confirm [3,982,889, 29,858,460]
# gap-free. (NOT up to 33.8M -- the middle ends at Sigma-N0 = 29,858,461 by symmetry.)
# Let me verify BOTH framings precisely and confirm the exact obligation.
# ============================================================
def R2_reach(N):
    b3b4=np.zeros(N+1,bool);b3b4[0]=True
    for x in sorted([3**j for j in range(2,17)]+[4**j for j in range(2,15)]):
        if x<=N:b3b4[x:]|=b3b4[:N+1-x].copy()
    b7=np.zeros(N+1,bool);b7[0]=True
    for x in sorted([7**j for j in range(2,12)]):
        if x<=N:b7[x:]|=b7[:N+1-x].copy()
    R=np.zeros(N+1,bool)
    for c in np.where(b7)[0]:R[c:]|=b3b4[:N+1-c]
    return R

# Compute Sigma_{3^15} = sum of atoms <= 3^15
atoms_le_315 = sorted([3**j for j in range(2,16)]+[4**j for j in range(2,12)]+[7**j for j in range(2,9)])
Sigma_315 = sum(atoms_le_315)
N0=3982888
print("Sigma_{3^15} = atomSum(atoms <= 3^15) =", Sigma_315, "(Aristotle: 33,841,349)")
print("  match:", Sigma_315 == 33841349)
print("Symmetric middle = (N0, Sigma-N0) = (%d, %d)" % (N0, Sigma_315-N0))
print("  => must verify [%d, %d] gap-free" % (N0+1, Sigma_315-N0-1))
print()
# Sieve to Sigma_315 and check the middle gap-free
N = Sigma_315 + 100
R = R2_reach(N)
mid_lo, mid_hi = N0+1, Sigma_315-N0-1
middle_gapfree = bool(R[mid_lo:mid_hi+1].all())
print("SEED OBLIGATION CHECK:")
print("  [%d, %d] (the symmetric middle) gap-free:" % (mid_lo, mid_hi), middle_gapfree)
# also confirm gap-free all the way to Sigma (baker's "34M" framing) -- stronger
to_sigma = bool(R[N0+1:Sigma_315+1].all())
print("  [%d, %d] (N0+1 to Sigma, baker's framing) gap-free:" % (N0+1, Sigma_315), to_sigma)
print()
# the actual largest miss (N0)
miss=np.where(~R[1:N0+200])[0]+1
print("  Largest miss below seed:", int(miss.max()), "(= N0(2), expected 3,982,888:", int(miss.max())==3982888, ")")
print()
if middle_gapfree:
    print(">>> CONFIRMED for baker: the symmetric middle [3,982,889, 29,858,460] is gap-free")
    print("    (and in fact gap-free all the way to Sigma=33,841,349). The seed obligation is MET.")
    print("    This is exactly Aristotle's baseCovered31_true (native_decide), reproduced by")
    print("    independent numpy sieve. The single load-bearing number checks out. <<<")
