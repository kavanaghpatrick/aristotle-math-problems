import math
# ============================================================
# Sub-check (2): does symmetric-doubling patch across finitely many FAILING atoms?
# Ridout gives: the gap lemma (star) v <= Sigma_V - 2N0 holds for all but FINITELY
# many atoms v. Question: can the induction absorb the finite exceptions?
#
# The doubling step needs (star) at EVERY atom above the base V0. If atom v* FAILS
# (star), the middle interval does NOT extend at that step -- a gap opens. BUT: if
# there are finitely many failing atoms, ALL below some bound B_exc, then we can
# choose the BASE V0 > B_exc (include all failing atoms IN the base). Then every
# atom above V0 satisfies (star), and the doubling closes.
#
# THE CATCH (the ineffectivity bite): Ridout does NOT tell us B_exc (where the
# exceptions stop). So we CANNOT compute/exhibit the base V0 > B_exc. The proof is
# NON-CONSTRUCTIVE: "there exists a finite base making it work" -- but we can't
# write it down. For a FIXED k this is still a valid (ineffective) EXISTENCE proof
# of cofiniteness (N0(k) exists, just not bounded). 
# ============================================================
print("Sub-check (2): does doubling patch across finitely many failing atoms?")
print()
print("YES, for FIXED k -- as an INEFFECTIVE existence proof:")
print("  Ridout => (star) fails for only finitely many atoms, all below some B_exc.")
print("  Choose base V0 > B_exc (absorb all failing atoms into the base set).")
print("  Then (star) holds for every atom > V0 => doubling closes => cofinite.")
print("  BUT Ridout doesn't give B_exc => V0 not computable => N0(k) exists but")
print("  is not bounded. Valid ineffective existence proof of cofiniteness AT FIXED k.")
print()
print("  ⚠ REQUIRES the base case I_k(V0) to be gap-free at that (unknown, large) V0.")
print("  And THAT is the Q2 obstruction: the base-case gap-freeness is NOT given by")
print("  Ridout -- it's a separate finite check at the (unknown) V0. For fixed k it's")
print("  'there exists a gap-free base' (true, since cofinite => eventually gap-free),")
print("  but this is CIRCULAR if used to PROVE cofiniteness. Need an INDEPENDENT reason")
print("  the base is gap-free. Aristotle's k=2 used native_decide for a SPECIFIC small V0;")
print("  the Ridout-ineffective V0 is large/unknown, so native_decide can't reach it.")
print()
print("  => Sub-check (2) verdict: doubling patches the finite exceptions ONLY if we")
print("     independently know the base is gap-free at V0>B_exc. For fixed k that's a")
print("     finite-but-unreachable check (V0 unknown). So Ridout gives at best a")
print("     CONDITIONAL ineffective proof: 'cofinite IF the (unknown) base is gap-free'.")
print("     The effective MW route AVOIDS this -- it gives a COMPUTABLE V0 we can sieve.")
print()
print("="*64)
print("Why did BEGL use EFFECTIVE MW when ineffective Ridout was available (1996)?")
print("="*64)
print("""
The answer is now clear from the reduction structure:
1. BEGL needed to EXHIBIT N0 = 581 (a SPECIFIC number) -- their claim is "the largest
   missing integer IS 581", a precise effective statement. Ridout gives only "finitely
   many missing, location unknown" -- it CANNOT produce 581. So for their stated result
   (exhibit the largest miss), effective MW is REQUIRED; Ridout is useless.
2. The effective MW bound gives a COMPUTABLE crossover, so the finite check terminates
   at a known point (their 581 computation). Ridout's ineffective finiteness cannot bound
   the computation -- you'd never know when to stop.
3. So BEGL's choice was FORCED by their goal (an exact N0), not an oversight. Ridout was
   available but gives a strictly weaker (ineffective, non-exhibiting) result. This also
   explains why the all-k tag is over-claimed: even ineffective Ridout doesn't give all-k
   (Q2 base case), and effective MW gives only the specific k they computed.
""")
