import math
N0 = 3982888
# Reproduce Aristotle's EXACT gapOK computation (Main.lean lines 83-93):
#   atoms = (3^e, 4^e, 7^e for e in 2..81).filter(<= cap).mergeSort(<=)
#   acc=0; for v in atoms: if v>3^15: assert acc >= v + 7965776; acc += v
# Note 7965776 = 2*N0 = 2*3982888. So check acc(before v) >= v + 2N0.
cap = 10**30
atoms = sorted([3**e for e in range(2,82)]+[4**e for e in range(2,82)]+[7**e for e in range(2,82)])
atoms = [a for a in atoms if a <= cap]
acc = 0
ok = True
minmargin = 10**40; argmin=None
fails=[]
for v in atoms:
    if v > 14348907:  # 3^15
        margin = acc - (v + 2*N0)
        if margin < minmargin: minmargin=margin; argmin=v
        if not (acc >= v + 2*N0):
            ok=False; fails.append((v,margin))
    acc += v
print("Reproducing Aristotle gapOK(10^30) EXACTLY:")
print("  result (all atoms in (3^15,10^30] satisfy acc>=v+2N0):", ok)
print("  min margin:", minmargin, "at v=", argmin)
if argmin:
    for b in (3,4,7):
        e=round(math.log(argmin,b))
        if b**e==argmin: print("    argmin = %d^%d" % (b,e))
print("  Aristotle claims: min +2,299,182 at 7^9. My min:", minmargin)
print("  failures:", len(fails), fails[:3])
print()
# MY EARLIER computation used atomSum_below(v) = sum of atoms < v (NOT running acc).
# The difference: 'acc' in Aristotle's loop = sum of all atoms PROCESSED BEFORE v in
# sorted order = sum of atoms < v (since sorted). SAME as atomSum_below(v). So why did
# I get negative? My earlier loop capped exponents at 40, but also -- KEY -- my earlier
# 'tail' loop computed atomSum_below via 'atoms_all' (exp<40), MISSING atoms with
# exponent 40..81 that are still < v for large v! For v=7^35, atoms like 3^50 < 7^35
# were missing. Let me confirm this was the bug:
atoms40 = sorted([3**e for e in range(2,40)]+[4**e for e in range(2,40)]+[7**e for e in range(2,40)])
v_test = 7**35
asb_capped = sum(a for a in atoms40 if a < v_test)
asb_full = sum(a for a in atoms if a < v_test)
print("BUG CHECK at v=7^35:")
print("  atomSum_below with exp<40 cap:", asb_capped, "(WRONG - missing high atoms)")
print("  atomSum_below full (exp<82):  ", asb_full)
print("  margin full:", asb_full - (v_test+2*N0), "(should be positive)")
