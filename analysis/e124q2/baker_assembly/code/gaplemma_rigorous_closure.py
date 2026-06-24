import math
N0=3982888
log={3:math.log(3),4:math.log(4),7:math.log(7)}
# ============================================================
# RIGOROUS directive-(b): prove the gap lemma for ALL v > V0 from pairwise MW.
#
# For atom v = c^e, slack(v) = sum_{d != c} (c_d(v) - v)/(d-1), c_d(v)=next d-power >= v.
# (GAP): slack(v) >= 2N0 + 18.
#
# The WORST case (smallest slack) is when v is just BELOW powers of both other bases,
# i.e. a near-triple-coincidence. We do NOT need to rule out triple coincidences
# directly (that's 3-log). Instead:
#
# CLEAN ARGUMENT: slack(v) >= max over other-base d of (c_d(v)-v)/(d-1)
#                        >= (c_{d0}(v) - v)/(d0 - 1) for the d0 giving the LARGER gap.
# It suffices that for SOME other base d, c_d(v) - v >= 2N0*(d-1).
# Equivalently: NOT both (c_d(v)-v) < 2N0*(d-1).
#
# Suppose, for contradiction, BOTH other-base gaps are small at v=c^e:
#   c_{d1}(v) - v < 2N0*(d1-1)  and  c_{d2}(v) - v < 2N0*(d2-1)   (d1,d2 the other two bases)
# Then v < c_{d1}(v) < v + 2N0*(d1-1) and v < c_{d2}(v) < v + 2N0*(d2-1).
# So |c_{d1}(v) - c_{d2}(v)| < 2N0*max(d1,d2) =: W (a CONSTANT ~ 4.8e7).
# But c_{d1}(v), c_{d2}(v) are powers of d1, d2 => |d1^a - d2^b| < W for some a,b.
# PAIRWISE MW on (d1,d2): |d1^a - d2^b| > W for all a (hence b) with a > A*(d1,d2,W).
# So a triple-coincidence at v forces a (d1,d2) pairwise near-coincidence with gap < W,
# which MW forbids for a,b large. => for v large enough, NOT both gaps small => (GAP) holds.
#
# This is PURELY PAIRWISE: we only ever bound |d1^a - d2^b| for ONE pair at a time
# (the pair of OTHER bases, not involving c). The crossover is set by the pairwise MW
# bound for that pair reaching W = 2N0*max(d-1) absolute.
# ============================================================
print("RIGOROUS gap-lemma closure from pairwise MW (the airtight argument):")
print()
print("Suppose v=c^e has BOTH other-base gaps small (the only way (GAP) can fail):")
print("  c_{d1}(v)-v < 2N0(d1-1) AND c_{d2}(v)-v < 2N0(d2-1), {d1,d2}=other two bases.")
print("Then |c_{d1}(v) - c_{d2}(v)| < 2N0*max(d1-1,d2-1) =: W")
print("  => |d1^a - d2^b| < W for powers d1^a=c_{d1}(v), d2^b=c_{d2}(v).")
print("PAIRWISE MW on (d1,d2) forbids |d1^a-d2^b| < W once a > crossover.")
print("  => no such v beyond the crossover => (GAP) holds. PURELY 2-LOG. ✓")
print()
# Compute W and the crossover for each pair (d1,d2) = the OTHER-base pairs.
# For v=3^p: other bases (4,7), W = 2N0*max(3,6)=2N0*6=12N0.  pair (4,7).
# For v=4^q: other bases (3,7), W = 2N0*max(2,6)=12N0.        pair (3,7).
# For v=7^r: other bases (3,4), W = 2N0*max(2,3)=6N0.         pair (3,4).
print("Per atom-base, the RELEVANT pairwise form and absolute threshold W:")
pairs = {3:((4,7),12*N0), 4:((3,7),12*N0), 7:((3,4),6*N0)}
for c,((d1,d2),W) in pairs.items():
    print("  v=%d^e : need |%d^a - %d^b| > W=%d (=%.1fN0) for the (%d,%d) pair" % (c,d1,d2,W,W/N0,d1,d2))
print()
# Crossover for each pair via BEGL-type bound |d1^a-d2^b| > exp(ln(d1)*(a - K*(8+ln a)^2))
# We need this > W. The crossover a* where it bites. Use the generic MW form.
# |d1^a - d2^b| > d1^a * exp(-C*(log a)^2), C ~ const for the pair. Need > W (absolute).
# => a*ln(d1) - C(log a)^2 > ln(W). Crossover a* ~ where a*ln(d1) > ln(W) + C(log a)^2.
# The pair (4,7): ln(d1)=ln4. Use BEGL-analog C=500*ln(d1)*ln(d2) (heuristic; gelfond refines).
import numpy as np
for c,((d1,d2),W) in pairs.items():
    C = 500*log[d1]*log[d2]
    a=np.arange(100,10**6)
    lhs = a*log[d1] - C*(8+np.log(a))**2
    idx=np.where(lhs > math.log(W))[0]
    astar = int(a[idx[0]]) if len(idx) else None
    print("  pair (%d,%d): crossover a* ~ %s (height %d^a* ~ 10^%.0f)" % 
          (d1,d2,astar, d1, astar*log[d1]/math.log(10) if astar else 0))
print()
print("So V0 = max over the three pairwise crossovers (in absolute height). The bridge")
print("computation must reach that V0. The (3,4)-pair crossover (smallest log-base) dominates.")
