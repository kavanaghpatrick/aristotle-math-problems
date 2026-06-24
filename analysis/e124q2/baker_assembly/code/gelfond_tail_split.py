"""
THE DECISIVE STRUCTURAL CHECK: BEGL96 proved k=1 (hole 581) WITH MW. How, if the bound is
vacuous at p=5? Because cofiniteness = (finite check up to N0) + (tail: no hole for n>N0).
The tail uses MW only for LARGE p, where the bound IS non-vacuous. The small p are checked
by direct computation.

So the real question for the comparison table:
  Is the NEEDED region (where a hole could form for n>N0) entirely in the p-range where the
  KNOWN bound is non-vacuous?

Map n -> p: a straggler near n sits at p ~ log_3(n). N0(k) grows ~7^k. For the ASYMPTOTIC
tail (all n > N0, all k), p ranges over ALL sufficiently large values. The bound must hold
for the worst convergent at each scale.
"""
import math
L3=math.log(3); L4=math.log(4)

def E_LMN(p, C0=25.2, c=0.38):
    bprime=p/L4+p/L3
    return C0*(math.log(max(bprime,math.e))+c)**2 * L3 * L4 / L3

# For the TAIL (large p), is E_LMN(p) <= 0.356*p (needed)? i.e. does the known bound
# eventually beat the needed threshold, and from where?
p=2; cross=None
while p<10**8:
    if E_LMN(p) < 0.356*p:
        cross=p; break
    p=int(p*1.05)+1
print(f"KNOWN two-log bound (C0=25.2) satisfies needed E_LMN(p) < 0.356p from p >= {cross:,}")
print(f"  At p={cross:,}: E_LMN={E_LMN(cross):.0f}, needed=0.356p={0.356*cross:.0f}")

# So the structure is:
#   - SMALL p (p < ~{cross}): finite set of convergents. Each checked by DIRECT computation
#     of |3^p-4^q| (exact integer). FINITE, decidable, no transcendence needed.
#   - LARGE p (p >= ~{cross}): the known explicit two-log bound DISCHARGES the needed inequality.
print(f"""
=== STRUCTURAL VERDICT ===
The needed inequality E(p) <= 0.356p splits at p* ~ {cross:,}:
  * TAIL  (p >= {cross:,}): KNOWN explicit two-log bound (Laurent/LMN) DISCHARGES it. [closes]
  * SMALL (p <  {cross:,}): finitely many convergents; each |3^p-4^q| is an EXACT integer,
    checkable by direct computation. NO transcendence needed -- just arithmetic.

So IF the only obstruction were the |3^p-4^q| spacing, the conjecture would close:
  (finite computation for p<p*) + (LMN bound for p>=p*).  => OUTCOME (a)/(b).

BUT: the team's Round-6 finding is that the bridge is NOT just |3^p-4^q|. It is the JOINT
covering (base-7 ray equidistributing across the B3+B4 gap bands). That needs the spacing
bound AT EVERY convergent simultaneously AND a covering-count margin (1.5-3x, FLAT).
""")

# Quantify: how many convergents are in the 'finite check' window p < p*?
def cf(x,n):
    a=[]
    for _ in range(n):
        ai=math.floor(x);a.append(ai);x-=ai
        if abs(x)<1e-13:break
        x=1/x
    return a
def conv(a):
    h=[0,1];k=[1,0];o=[]
    for ai in a:
        h.append(ai*h[-1]+h[-2]);k.append(ai*k[-1]+k[-2]);o.append((h[-1],k[-1]))
    return o
C=conv(cf(L4/L3,40))
small=[(p,q) for (p,q) in C if 1<=p<cross]
print(f"Convergents p/q of log4/log3 with p < p*={cross:,} (the FINITE-CHECK set): {len(small)} of them")
print("  p-values:", [p for p,q in small])
print(f"\n=> The 'finite check' is genuinely finite: ~{len(small)} convergent scales, each an exact")
print("   integer spacing. This is the difference between OUTCOME (b) sharp-conditional and (c) wall.")
