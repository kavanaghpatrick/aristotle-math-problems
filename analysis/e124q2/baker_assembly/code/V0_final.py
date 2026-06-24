import math
N0=3982888
log={3:math.log(3),4:math.log(4),7:math.log(7)}
# Final V0: the bridge must reach max over atom-bases of the (other-pair) MW crossover height.
# Computed (BEGL C=500 heuristic): (4,7) pair binding at height 10^257505 (atom base 3).
maxheight=257505  # log10
print("CORRECTED V0 for the gap-lemma bridge:")
print("  Aristotle PROOF_NOTES: V0=3^293903 ~ 10^140227 (uses (3,4) pair only) -- INSUFFICIENT")
print("  Correct V0 ~ 10^257505 (the (4,7) pair, binding for atom base 3) with BEGL C=500")
print()
# atom count and bridge cost
n_atoms = sum(max(0, int(maxheight*math.log(10)/log[b])-1) for b in (3,4,7))
print("  Atoms in [3^15, 10^257505]: ~%d" % n_atoms)
print("  Max digit size ~257505; digit-ops ~%.1e" % (n_atoms*maxheight))
print("  Python bigint scaling ~p^2: ~%.1fx the 3^293903(=10^140227) run" % ((257505/140227)**2))
print("  If the 3^293903 run is ~10 min, the corrected V0 run is ~%.0f min." % (10*(257505/140227)**2))
print()
print("IMPORTANT CAVEATS:")
print("1. This is the BEGL C=500 HEURISTIC crossover. The actual Laurent-2008 constants")
print("   (gelfond/rhin) for (4,7) and (3,7) will shift it -- likely SMALLER (sharper).")
print("2. The (4,7) and (3,7) pairs have DIFFERENT CF bases (log4/log7=0.712, log3/log7=0.565)")
print("   than the well-studied (3,4) (log3/log4=0.792). Their close-pair structure differs;")
print("   the crossover depends on the actual MW constant for each.")
print("3. Empirically (GAP) holds with margin >=+2.3M for ALL atoms to 10^60 already -- the")
print("   crossover is where it's GUARANTEED, far beyond where it's TRUE. The bridge proves")
print("   it on [3^15, V0]; MW proves it on (V0, inf).")
print()
print("=> The bridge is FEASIBLE either way (~30-60 min Python for the corrected V0), but the")
print("   EXACT V0 depends on gelfond/rhin's per-pair Laurent constants. FLAG to team-lead +")
print("   gelfond: Aristotle's single-pair V0 is an underestimate; need all 3 pairwise crossovers.")
