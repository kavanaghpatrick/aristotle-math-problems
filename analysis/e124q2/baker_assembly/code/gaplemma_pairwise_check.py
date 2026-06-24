import math
log3=math.log(3); log4=math.log(4); log7=math.log(7)
N0=3982888
# ============================================================
# CRITICAL for (b): is the gap lemma a PAIRWISE (2-log) statement, or does the
# worst case need a TRIPLE coincidence (3-log)?
#
# atomSum(<v) for v=3^p: the slack above the elementary v-18 bound is
#   slack = (c_4(v)-v)/3 + (c_7(v)-v)/6  [distances to next 4-power and 7-power].
# For (GAP) to FAIL we'd need slack < 2N0+18, i.e. BOTH (c_4(v)-v)/3 AND (c_7(v)-v)/6
# small simultaneously => c_4(v) close to v AND c_7(v) close to v => 4^{q+1}≈3^p≈7^{r+1}
# a TRIPLE coincidence. 
#
# BUT: for the gap lemma we only need slack >= 2N0 (a CONSTANT). The slack is a SUM.
# Even if ONE term collapses (say 4^{q+1}≈3^p, MW-close), the OTHER term (c_7(v)-v)/6
# is generically ~ v (since 7-powers are sparse, the next 7-power is typically far).
# For (GAP) to fail, we need BOTH terms < 2N0 simultaneously. Since 2N0~8e6 is a fixed
# constant and v grows, "both terms < 8e6" means v is within 8e6 (absolute) of BOTH a
# 4-power AND a 7-power from below -- TWO simultaneous near-coincidences.
#
# So the worst case for (GAP) failing IS a triple coincidence (needs both). BUT the
# question is whether we need to RULE OUT triple coincidences (3-log, harder) or whether
# pairwise (2-log) suffices. Let me check: is ruling out "both terms small" reducible
# to two SEPARATE pairwise statements?
# ============================================================
print("Is (GAP)-failure a pairwise or triple-coincidence event?")
print()
print("slack(v=3^p) = (c_4(v)-v)/3 + (c_7(v)-v)/6.  (GAP) fails iff slack < 2N0+18.")
print("For the SUM < 2N0, need BOTH (c_4-v)/3 < 2N0 AND (c_7-v)/6 < 2N0 (else one term alone >= 2N0).")
print("  (c_4(v)-v)/3 < 2N0  <=>  c_4(v) < v + 6N0  <=>  next 4-power within 6N0 of v (absolute)")
print("  (c_7(v)-v)/6 < 2N0  <=>  c_7(v) < v + 12N0 <=> next 7-power within 12N0 of v")
print()
print("So (GAP) failure needs v with a 4-power in (v, v+6N0] AND a 7-power in (v, v+12N0].")
print("For LARGE v, the windows 6N0, 12N0 are RELATIVELY tiny (6N0/v -> 0).")
print()
# Reframe as PAIRWISE: if v=3^p, and there's a 4-power 4^{q+1} in (3^p, 3^p+6N0],
# that's |4^{q+1}-3^p| <= 6N0, a pairwise (3,4) close approach (absolute gap <= 6N0).
# MW bounds |3^p-4^Q| from below => for large p, |3^p-4^Q| > 6N0 (absolute), so NO
# 4-power that close => (c_4(v)-v)/3 >= 2N0 alone => slack >= 2N0 => (GAP) holds.
# THIS IS PURELY PAIRWISE (3,4)! We don't even need the 7-term.
print("KEY: (GAP) holds as soon as EITHER (c_4(v)-v)/3 >= 2N0 OR (c_7(v)-v)/6 >= 2N0.")
print("To GUARANTEE (GAP), enough that ONE of the two other-base gaps is >= the constant.")
print("For v=3^p: |3^p - 4^Q| > 6N0 (absolute) for large p [pairwise (3,4) MW] => done,")
print("regardless of the 7-power. So (GAP) reduces to TWO PAIRWISE statements, and holds")
print("if EITHER pairwise gap is large -- we need BOTH pairwise gaps small to fail.")
print()
# Verify: for which atoms v could BOTH gaps be < their thresholds? Check empirically.
N=10**8
print("Checking atoms v in (3^15, 10^40]: is (GAP) ever close to failing (slack < 4N0)?")
atoms=sorted([(3**e,3,e) for e in range(2,90)]+[(4**e,4,e) for e in range(2,90)]+[(7**e,7,e) for e in range(2,90)])
def next_power_above(v, base):
    e=math.ceil(math.log(v)/math.log(base)-1e-12)
    p=base**e
    while p<=v: e+=1; p=base**e
    return p
worst=10**60; argw=None
for v,base,e in atoms:
    if v<=14348907 or v>10**40: continue
    slack=0
    for d in (3,4,7):
        if d==base: continue
        cd=next_power_above(v,d)
        slack += (cd - v)//(d-1)
    margin = slack - 2*N0
    if margin<worst: worst=margin; argw=(v,base,e)
print("  min slack-margin (slack - 2N0) over atoms (3^15,10^40]:", worst)
print("  at v=%d^%d" % (argw[1],argw[2]))
print("  (>0 means GAP holds with room; matches Aristotle min +2,299,182 at 7^9 region)")
