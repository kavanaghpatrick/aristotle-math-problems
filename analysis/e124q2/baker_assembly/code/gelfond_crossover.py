"""
Where does the explicit two-log bound become NON-VACUOUS (E_LMN < p)?
And cross-check vs BEGL96's OWN displayed bound:
  |3^p - 4^q| > exp{ ln3*(p - 500*ln4*(8+ln p)^2) }
  => E_BEGL(p) = 500*ln4*(8+ln p)^2   (the loss exponent in base 3)
"""
import math
L3=math.log(3); L4=math.log(4)

def E_LMN(p, C0=25.2, c=0.38):
    bprime=p/L4+p/L3
    return C0*(math.log(max(bprime,math.e))+c)**2 * L3 * L4 / L3
def E_BEGL(p):
    return 500*L4*(8+math.log(max(p,2)))**2   # already in base-3 loss exponent units (factor ln3 cancels)

print("Crossover: smallest p with guaranteed E(p) < p (bound becomes non-vacuous):")
for name,fn in [("LMN/Laurent C0=25.2",E_LMN),("BEGL96 displayed (C=500)",E_BEGL)]:
    p=2
    while p < 10**7:
        if fn(p) < p: break
        p=int(p*1.2)+1
    print(f"  {name:28s}: non-vacuous from p ~ {p:,}  (E={fn(p):.0f} < p={p:,})")

print("\nWhere do the ACTUAL holes / stragglers live (in p-units)?")
print("  k=1 hole 581  ~ 3^5..3^6     => p ~ 5-6")
print("  k=2 N0=3.98M  ~ 3^13..3^14   => p ~ 13-14")
print("  k=3 N0=166M   ~ 3^17         => p ~ 17")
print("  CF convergents with actual close pairs: p = 5, 19, 23, 24, 29, 42, 53, ...")
print("\n=> The stragglers that DECIDE cofiniteness sit at p ~ 5-53.")
print("   The explicit two-log bound is VACUOUS there (needs p in the thousands+).")

# But: the bound only has to beat the NEEDED loss, which is NOT 'E<p' (full collapse).
# The bridge needs: rel spacing >= (covering deficit) ~ 1/(base-7 shift count) ~ n^{-0.356} ~ 3^{-0.356 p}.
# So NEEDED: E(p) <= 0.356*p  (the spacing must exceed the base-7 covering granularity).
print("\n=== REFINED NEEDED threshold: E(p) <= 0.356*p (base-7 covering granularity n^0.356) ===")
print(f"{'p':>4} {'E_actual':>9} {'E_needed=0.356p':>15} {'actual<needed?':>15} {'E_LMN guar':>11} {'LMN<needed?':>12}")
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
C=conv(cf(L4/L3,15))
for (p,q) in C:
    if p>200: break
    if p<1: continue
    P=3**p; d=abs(P-4**q)
    if d==0: continue
    Eact=-math.log(d/P)/L3
    Eneed=0.356*p
    Elmn=E_LMN(p)
    print(f"{p:>4} {Eact:>9.3f} {Eneed:>15.3f} {str(Eact<Eneed):>15} {Elmn:>11.1f} {str(Elmn<Eneed):>12}")
print("\nINTERPRETATION:")
print(" - 'actual<needed' TRUE  => the TRUE spacing IS wide enough (hole gets covered). This is WHY")
print("   the conjecture is true empirically.")
print(" - 'LMN<needed' FALSE at every small p => the KNOWN bound CANNOT certify it at the deciding")
print("   convergents. The known explicit constant is ~100x too weak in the exponent at p~5-53.")
