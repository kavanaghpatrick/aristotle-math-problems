"""
THE DECISIVE COMPARISON: the covering inequality, needed vs known, AT the convergent arcs.

The bridge (lift_bridge_quantified, INV-S10) needs, at each convergent-arc scale:
   #(base-7 subset-sums available below U) >= #(shifts needed to cover the B3+B4 gap)
Equivalently (S10/Riesz form): min(P_3,P_4,P_7) <= C*rho^L on the danger arcs, rho<1.

Measured INPUTS (the campaign's real data):
  - base-7 covering margin = (avail)/(needed) = 1.5-3.0x, FLAT (non-growing). [lift_bridge_quantified]
  - S10 min-product decay: L=6->0.242, 8->0.204, 10->0.119, 12->0.048 (k-uniform). [scholar/breaker]
  - per-atom minor-arc decay c in [0.17,0.31] (boundary), [0.31] strict. [breaker_S10_boundary]
  - convergent-arc S_4 cancellation LOSS: a=4->0.001,5->0.057,9->0.221,14->0.369,19->0.564->log2
    (base-4 sum loses ALL cancellation on deep 3-adic convergent arcs). [troika Round 6]

So on the convergent arcs the analytic decay is DEGRADED but the MIN over the three rays still
decays (some ray always small). The QUESTION: does the KNOWN decay rate beat the NEEDED margin?
"""
import math

print("=== COVERING-MARGIN COMPARISON at the convergent arcs ===\n")
# The needed: min-product must be <= the covering threshold so that the joint cover closes.
# Needed margin in the covering inequality = 1 (it's a tight >=1 inequality, FLAT).
# Known/measured: the min-product decay gives an EFFECTIVE margin = (decay headroom).

# S10 min-product values (max over danger theta) vs the trivial 'no decay' = 1.0
S10 = {6:0.242, 8:0.204, 10:0.119, 12:0.048}
print("INV-S10 min-product (max over danger arcs of min(P3,P4,P7)); 1.0 = no decay (would FAIL):")
print(f"{'L':>4} {'min-prod':>9} {'headroom=1/val':>15} {'needed':>8} {'margin ratio':>13}")
for L,v in S10.items():
    head=1/v
    # needed: the product must be below the L1-normalized covering threshold ~ rho_cover.
    # The campaign's covering margin is 1.5-3x FLAT; express the S10 headroom growth vs that.
    print(f"{L:>4} {v:>9.3f} {head:>15.2f} {'~1 (tight)':>8} {head:>13.2f}")

print("""
KEY TENSION (the trap the mission flagged):
  - The S10 min-product DECAYS (0.242 -> 0.048 over L=6..12), so its HEADROOM GROWS (4x -> 21x).
    This LOOKS like comfortable, growing margin.  <-- the apparent good news (scholar's read)
  - BUT lift's DIRECT covering-count margin (avail/needed base-7 shifts) is FLAT at 1.5-3x.
    <-- the criticality signature at the boundary sum=1
  These two are NOT the same margin. The S10 headroom is an AVERAGE-decay (minor-arc INTEGRAL),
  while cofiniteness needs a POINTWISE bound at the straggler (maverick's large-deviation kill:
  at N0=3,982,888, Phi=0 while E[Phi]=56 -- a 5.3-sigma event the average cannot see).
""")

# The decisive number: convergent-arc S_4 cancellation loss vs the needed.
print("=== The convergent-arc cancellation LOSS (troika Round 6) -- the wall in numbers ===")
loss = {4:0.001, 5:0.057, 9:0.221, 14:0.369, 19:0.564}
print(f"{'a (3-adic conv depth)':>22} {'log|S4|/nt4 LOSS':>17} {'cancellation left':>18}")
for a,v in loss.items():
    print(f"{a:>22} {v:>17.3f} {1-v/math.log(2):>18.3f}")
print(f"  (log2 = {math.log(2):.3f} = total available cancellation; loss->log2 means NONE left)")
print("""
=> On the DEEP convergent arcs, S_4 keeps ~0 cancellation (loss -> log2). The minor-arc decay
   that the KNOWN harmonic-analytic estimate would supply is ABSENT exactly there. The only thing
   that saves the bound is the SPACING |3^a-4^b| keeping the arc NARROW (3-adic) -- which is the
   MW input. So the known analytic decay does NOT discharge the convergent arcs; the MW spacing
   bound is REQUIRED, and (per the finite/tail split) it discharges them EXCEPT it must be paired
   with the covering-count margin, which is FLAT (no slack) at the boundary.
""")
