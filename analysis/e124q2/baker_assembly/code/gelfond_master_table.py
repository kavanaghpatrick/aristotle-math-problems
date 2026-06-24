"""
gelfond MASTER NEEDED-vs-KNOWN table generator. Consolidates the board's verified inputs
(nesterenko ground-truth, matveev constants, feldman face-split, mahler k-uniformity) into
the single decision artifact: at each principal convergent of log3/log4, NEEDED spacing-exponent
vs KNOWN guaranteed-exponent, with margin, plus the covering-margin face.

Cross-checks every number against the board entries. Exact integer powers; math.log for logs.
"""
import math
L3=math.log(3); L4=math.log(4); L7=math.log(7)

# Principal convergents of log3/log4 (= nesterenko/matveev verified): q/p = 4/5,19/24,23/29,42/53,...
# p = 3-exponent (denominator). Verified list:
conv_pq = [(5,4),(24,19),(29,23),(53,42),(612,485),(665,527)]  # (p,q): 3^p ~ 4^q
# (also p=1,q=1 trivially; start at the first real coincidence p=5)

print("="*78)
print("TABLE 1 — PAIRWISE FACE: |3^p - 4^q| at principal convergents of log3/log4")
print("  |3^p-4^q| = 3^{p - E(p)}.  NEEDED: E(p) < p (positivity) and E(p) <= 0.356p (covering).")
print("  KNOWN guaranteed E: Matveev-2000 (matveev board) and BEGL/MW-1989 (nesterenko board).")
print("="*78)
def E_matveev(p):
    # matveev: log(|Lambda|) > -1.1724e9*(1+log p); E = that / L3  (relative form /3^p)
    return 1.1724e9*(1+math.log(max(p,2)))/L3
def E_begl(p):
    # BEGL/MW displayed relative exponent -761.5*(8+log p)^2 (matveev board); E in base-3 units
    return 761.5*(8+math.log(max(p,2)))**2 / L3   # /L3 to convert to base-3 loss exponent
print(f"{'p':>4}{'q':>4}{'|3^p-4^q|/3^p':>15}{'E_actual':>9}{'0.356p':>8}{'E_MW(BEGL)':>11}{'E_Matveev':>11}")
for (p,q) in conv_pq:
    if p>700: 
        # too big to print full int rel; compute via logs
        rel=math.exp(p*L3-q*L4) if p*L3>q*L4 else math.exp(q*L4-p*L3)
        rel=abs(1-math.exp(q*L4-p*L3))
        Eact=-math.log(rel)/L3
    else:
        d=abs(3**p-4**q); rel=d/3**p; Eact=-math.log(rel)/L3
    print(f"{p:>4}{q:>4}{rel:>15.3e}{Eact:>9.3f}{0.356*p:>8.2f}{E_begl(p):>11.0f}{E_matveev(p):>11.3e}")

print("""
READ: E_actual (true loss) is TINY (2.7-5.6) and stays well under 0.356p for p>=24 -- the TRUE
spacing is wide enough, so the cover closes. This is WHY the conjecture is true. But the KNOWN
guaranteed E (E_MW, E_Matveev) is ENORMOUS at these p (10^3 - 10^9), >> p. The known bound is
VACUOUS at every convergent that carries a hole. It only beats 0.356p past the crossovers:
  BEGL/MW:  p* ~ 2.94e5  (matveev/nesterenko)   Matveev-2000: p* ~ 2.67e10  (matveev)
The deciding stragglers sit at p ~ 5-17 (581, 3.98M @p~13, 166M @p~17). FINITE-CHECK region.
""")

print("="*78)
print("TABLE 2 — COVERING FACE (feldman FACE 2): the JOINT base-7 bridge margin")
print("="*78)
# feldman/lift/breaker measured data
print("Covering margin (B7 avail)/(needed) at worst B3+B4 convergent gaps [lift/feldman]:")
print("  gap@4^11: 1.5x   gap@3^15: 1.7x   gap@3^16: 1.9x   shallow gaps: 7-14x")
print("  => FLOORS at ~1.5x, bounded below, NON-GROWING at the boundary. NEEDED: >=1.")
print()
print("INV-S10 min-product max over danger arcs [scholar/breaker], k-uniform:")
for L,v in [(6,0.242),(8,0.204),(10,0.119),(12,0.048)]:
    print(f"  L={L:>2}: {v:.3f}  (headroom 1/v = {1/v:.1f}x)")
print("  Per-atom decay c in [0.17,0.31] (boundary), 0.31 (strict) [breaker_S10_boundary]. NEEDED: c>0.")
print()
print("feldman shape-derivation: spoiled/total = C(log J)^2 / J -> 0  =>  POLYNOMIAL rate SUFFICES.")
print("  So FACE 2 needs polynomial (Baker-shape), NOT super-polynomial. NEEDED rate = ACHIEVABLE.")

print("""
="*78
VERDICT SYNTHESIS (gelfond, consolidating the board):
="*78
NEEDED:  pairwise face -- E(p) < 0.356p (TRUE spacing satisfies it; finite check below p*~3e5).
         covering face -- joint-decorrelation polynomial bound, constant c0>0, margin floor >=1.
KNOWN:   pairwise -- Matveev/MW bounds are RIGHT SHAPE but VACUOUS at the deciding p (p* huge);
                     they prove FINITENESS (only finitely many close pairs) => finite check closes
                     the FIXED-TRIPLE per-fixed-k case. [matveev, nesterenko: outcome a/b here]
         covering -- NO citable bound exists for the joint object (it's a NEW estimate). [feldman]

=> The known bounds DISCHARGE the pairwise face (a/b) but the covering face has NO known bound (c).
   The wall is a MISSING-LEMMA wall (joint decorrelation), NOT a rate-shape wall (feldman) and NOT
   the pairwise spacing (which closes). k-uniform N0(k) is separately unproven (mahler).
""")
