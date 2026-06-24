from fractions import Fraction
import math
# ============================================================
# EXACT proof that S(a-)/a > 1 for every atom a = base^J, J>=2, base in {3,4,7}.
# No floats. The claim: sum of ALL atoms strictly less than a, exceeds a.
#
# For atom a = c^J (c in {3,4,7}):
#   OWN ray: sum_{j=2}^{J-1} c^j = (c^J - c^2)/(c-1).   [for c=3: (a-9)/2]
#   OTHER ray base b: let m = largest exp with b^m < a (m>=2 if b^2<a).
#       sum_{j=2}^{m} b^j = (b^{m+1} - b^2)/(b-1).
#   We need: OWN + sum over other b of OTHER_b  >  a.
#
# Lower bound per other ray: b^{m+1} > a (def of m), so
#   (b^{m+1}-b^2)/(b-1) > (a - b^2)/(b-1).
# Own ray: (a - c^2)/(c-1).
# So S(a-) > (a-c^2)/(c-1) + sum_{b != c} (a - b^2)/(b-1).
#   = a * [1/(c-1) + sum_{b!=c} 1/(b-1)] - [c^2/(c-1) + sum_{b!=c} b^2/(b-1)]
#   = a * [sum_all 1/(b-1)] - [sum_all b^2/(b-1)]
#   = a * beta - K,   where beta = 1/2+1/3+1/6 = 1, K = 9/2+16/3+49/6 = const.
# So S(a-) > a*1 - K = a - K.   Hence S(a-)/a > 1 - K/a.
# This gives S(a-) > a - K, i.e. a < S(a-) + K. NOT quite a <= S(a-).
# So (*) [a <= 1 + S(a-)] needs S(a-) >= a-1, i.e. the deficit K must be beaten.
K = Fraction(9,2)+Fraction(16,3)+Fraction(49,6)
print("beta = 1/2+1/3+1/6 =", Fraction(1,2)+Fraction(1,3)+Fraction(1,6))
print("K = 9/2 + 16/3 + 49/6 =", K, "=", float(K))
print()
print("LOWER BOUND: S(a-) > a*beta - K = a - %.3f" % float(K))
print("This gives S(a-) > a - 16.5. So a < S(a-) + 16.5, i.e. a - S(a-) < 16.5.")
print("(*) needs a <= 1 + S(a-), i.e. a - S(a-) <= 1. The crude bound only gives <16.5.")
print()
print("So the CRUDE harmonic bound is NOT enough -- there's a gap of up to ~16.")
print("This is the 9/(2a)-type deficit made precise: the inequality a<=1+S(a-) is")
print("NOT guaranteed by the harmonic sum alone; it needs the STRICT slack b^{m+1}>a")
print("to be quantitatively > the deficit. Let me compute the EXACT a-S(a-) for atoms")
print("to see if it's ever > 1 (which would break the simple (*)).")
print()
def atoms_below_sum(a):
    s=0
    for b in (3,4,7):
        j=2; p=b*b
        while p<a: s+=p; j+=1; p*=b
    return s
worst_def=-10**9; worst=None
viol=[]
for b in (3,4,7):
    for J in range(2,300):
        a=b**J
        if a<=3982888: continue
        if a>10**120: break
        S=atoms_below_sum(a)
        deficit=a-S   # if >1, (*) fails for single-append
        if deficit>worst_def: worst_def=deficit; worst=(b,J,a)
        if deficit>1: viol.append((b,J,deficit))
print("max (a - S(a-)) over atoms a in (N0,10^120):", worst_def, "at %d^%d"%(worst[0],worst[1]))
print("atoms where a - S(a-) > 1 (single-append (*) FAILS):", len(viol))
for b,J,d in viol[:10]:
    print("   %d^%d: a-S(a-) = %d" % (b,J,d))
