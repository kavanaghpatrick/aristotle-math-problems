"""
KNOWN side: explicit two-log lower bound on Lambda = |q log4 - p log3| = |p log3 - q log4|,
which controls |3^p - 4^q| via |3^p - 4^q| = 3^p * |1 - 4^q/3^p| ~ 3^p * |Lambda| (when small).

We use the Laurent-Mignotte-Nesterenko / Laurent 2008 two-log form (the standard citable bound
BEGL96 invoked Mignotte-Waldschmidt 1989 Cor 10.1 for the SAME quantity).

Generic two-log lower bound shape (Laurent 2008, Thm 2, m=10 / Corollary form):
  log|Lambda| >= -C1 * (log A1)(log A2) * (max(log b', ...))^2
where A1,A2 are heights (log A_i >= log alpha_i), b' is the height of the exponent pair.
For alpha1=3, alpha2=4: log A1 = log3=1.0986, log A2=log4=1.386.
b' ~ p/log A2 + q/log A1  (Laurent's b'); for our convergents p~q so b'~ p*(1/log4+1/log3).
The decisive feature: the (log b')^2 factor => log|Lambda| >= -C * (log p)^2.
"""
import math
L3=math.log(3); L4=math.log(4)

# Laurent 2008 'Linear forms in two logarithms' explicit constant.
# The well-known explicit corollary (Laurent-Mignotte-Nesterenko 1995, also Laurent 2008):
#   log|Lambda| > -25.2 * (max{ log b' + 0.38, 21/13, ... })^2 * logA1 * logA2  (schematic; m,C(m) chosen)
# We use a representative explicit constant C0 for the (log b')^2 * logA1 * logA2 form.
# Exact constants are task #22/#23/#24's job; here we bracket with the standard ranges:
#   - LMN 1995 / Laurent 2008 m=10: leading constant ~ 24-25 (times the squared log)
#   - The empirically-fitted constant from our data (E124_UNIFIED: C ~ 1.22 in |3^p-4^q|>=3^p exp(-C(log p)^2))

print("=== NEEDED vs KNOWN loss-exponent E(p) where |3^p-4^q| = 3^{p-E(p)} ===\n")
print("NEEDED (to discharge the bridge / kill the last straggler): E(p) must stay BELOW the")
print("threshold at which a hole survives. From BEGL96 k=1: the bound only has to beat the local")
print("covering deficit. The needed condition is E(p) = o(p) (sub-linear) -- a relative spacing")
print("that doesn't collapse faster than the base-7 covering density n^0.356 can repair.\n")

# Empirical needed: from troika/lift, the hole 581 forms where rel gap ~0.05 (p=5). The margin
# (avail/needed base-7 shifts) is 1.5-3x and FLAT. So 'needed' E(p) is the value beyond which
# margin<1. Let's express both as functions of p.

print(f"{'p':>4} {'q':>4} {'E_actual':>9} {'E_MW_LMN':>10} {'E_emp1.22':>10} {'margin=K/N':>11} {'verdict':>8}")
# convergents
def cf(x,n):
    a=[];
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

def E_LMN(p):
    # log|Lambda| >= -C0*(log b'+c)^2 * L3 * L4 ; E = -log_3|3^p-4^q| shift = (that)/L3
    bprime = p/L4 + p/L3   # p~q
    C0=25.2; c=0.38
    logLam_lb = -C0*(math.log(max(bprime, math.e))+c)**2 * L3 * L4
    # |3^p-4^q| ~ 3^p*|Lambda|  => log_3|3^p-4^q| ~ p + logLam_lb/L3 ; E = -(logLam_lb/L3)
    return -logLam_lb/L3
def E_emp(p):
    # empirical fit C=1.22: |3^p-4^q| >= 3^p exp(-1.22(log p)^2) => E = 1.22(log p)^2/L3
    return 1.22*(math.log(max(p,2)))**2 / L3

for (p,q) in C:
    if p>200 or p<1: 
        if p>200: break
        continue
    P=3**p; d=abs(P-4**q)
    if d==0: continue
    Eact=-math.log(d/P)/L3
    Elmn=E_LMN(p); Eemp=E_emp(p)
    # 'needed' = p (full collapse would be E=p, rel gap ~ O(1/3^p)); margin in EXPONENT terms:
    # the bound guarantees spacing 3^{p-Elmn}; a hole needs spacing < (covering reach). 
    # Margin = (p - Elmn)/(p - E_needed_for_hole). Use needed-collapse fraction: hole survives if E~p.
    margin = (p - Elmn)/p if p>0 else 0   # fraction of full size the KNOWN bound guarantees
    verdict = "OK" if Elmn < p else "FAIL"
    print(f"{p:>4} {q:>4} {Eact:>9.3f} {Elmn:>10.2f} {Eemp:>10.3f} {margin:>11.4f} {verdict:>8}")

print("\nNOTE: E_MW_LMN is the GUARANTEED loss; E_actual is the TRUE loss; E_emp is the fitted MW shape.")
print("KNOWN bound is valid iff E_MW_LMN < p (spacing stays positive-exponent). margin = (p-E_LMN)/p.")
