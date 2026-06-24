from fractions import Fraction
import math
# ============================================================
# PROVE FOREVER: S(a-) >= a for every atom a = c^J (J>=2, c in {3,4,7}), a > some small bound.
#
# Refined lower bound. For atom a=c^J, and another base b, let m=floor(log_b a)
# (largest b^m < a, assuming b^m != a which holds since bases mult. independent
# except we must check b^m < a strictly -- true for distinct bases, powers never equal).
# The b-ray sum below a = (b^{m+1}-b^2)/(b-1). Now b^{m+1} > a, and MORE: b^{m+1} = b*b^m,
# and b^m > a/b, so b^{m+1} > a. The slack: b^{m+1} - a = b^m(b - a/b^m) ... 
# Better: b^{m+1}/a = b^{m+1}/a > 1, and b^{m+1}/a <= b (since b^m < a => b^{m+1} < ab).
# So b-ray sum > (a - b^2)/(b-1), giving the crude beta bound.
#
# The REAL slack: at least ONE other base b has b^{m+1} comfortably > a (not just barely).
# But the worst case is when ALL other bases have b^{m+1} JUST above a (triple coincidence).
# Triple coincidence 3^p ~ 4^q ~ 7^r is bounded away by Baker. BUT the computation shows
# a - S(a-) <= -556064 always, hugely negative -- so even the WORST near-coincidence leaves
# S(a-) >> a. Why is the empirical margin so huge vs the crude '< 18'?
# Because: the crude bound replaced b^{m+1} by a (its min), but ALSO the b-ray has MANY
# terms; and the OWN ray (c^J-c^2)/(c-1) is ~a/(c-1) which for c=3 is a/2, for c=4 is a/3,
# for c=7 is a/6. Plus the FULL other rays. Let me get the EXACT asymptotic worst margin.
# ============================================================
def S_below(a):
    s=0
    for b in (3,4,7):
        p=b*b
        while p<a: s+=p; p*=b
    return s

# The ratio (S(a-) - a)/a = excess fraction. Find its infimum over atoms exactly.
# excess = S(a-)/a - 1. We computed min S/a = 1.0098 at 3^294. So min excess = 0.0098.
# 0.0098 * 3^294 is astronomically large in absolute terms (hence -556064 was just the
# small-a regime; for large a the absolute margin S(a-)-a GROWS like 0.0098*a).
# So S(a-) - a >= 0.0098 * a > 0 for all a -- IF inf(S/a) = 1.0098 > 1 holds forever.
print("The absolute margin S(a-)-a = (S/a - 1)*a. Since min(S/a)=1.0098 (at 3^294),")
print("S(a-)-a >= 0.0098*a, which GROWS with a. The -556064 'max deficit' was actually")
print("NEGATIVE (a always < S), confirming S(a-) > a always. Recheck the sign:")
for b,J in [(4,11),(3,294),(4,42),(7,2)]:
    a=b**J; S=S_below(a)
    print("  %d^%d: a=%d, S(a-)=%d, S-a=%d, S/a=%.5f" % (b,J,a,S,S-a,Fraction(S,a)))
print()
# Now PROVE inf(S/a) > 1 forever. S/a = own + sum_other. Worst = 3^p with 4,7 powers
# both just below their 'a/b' floor. The asymptotic inf is exactly 1 (shown). So inf is
# NOT bounded away from 1 by an elementary constant -- it's approached at deep coincidences.
# BUT: does it ever EQUAL or go BELOW 1? That needs S/a > 1 i.e. the STRICT inequalities
# rho4 > 1/4, rho7 > 1/7 to beat the 3-ray deficit (c^2/(c-1))/a = 9/(2a).
print("RIGOROUS: S(a-)/a = [3-ray]/a + [4-ray]/a + [7-ray]/a.")
print("For a = 3^p (the binding case):")
print("  3-ray/a = (3^p - 9)/(2*3^p) = 1/2 - 9/(2a)")
print("  4-ray/a = (4^{q+1}-16)/(3a), q=largest with 4^q<a; 4^{q+1}>a so > (a-16)/(3a)=1/3-16/(3a)")
print("  7-ray/a = (7^{r+1}-49)/(6a), 7^{r+1}>a so > 1/6 - 49/(6a)")
print("  SUM > 1/2+1/3+1/6 - (9/2+16/3+49/6)/a = 1 - 18/a.")
print("  So S(a-)/a > 1 - 18/a, i.e. S(a-) > a - 18.  ==> a - S(a-) < 18.")
print()
print("To get a <= S(a-) (margin for (*)), need to beat the 18. The 4^{q+1}>a and 7^{r+1}>a")
print("are STRICT with integer slack: 4^{q+1} >= a+1 is NOT enough, but the actual values")
print("4^{q+1}, 7^{r+1} EXCEED a by a POSITIVE FRACTION unless triple-coincident.")
print()
print(">>> CONCLUSION: a - S(a-) < 18 ALWAYS (elementary). For atoms a > 18, this does NOT")
print("    immediately give a <= S(a-). BUT the window-propagation lemma does not actually")
print("    need (*) per-atom -- it needs the WINDOW to not be overtaken. Re-examine: <<<")
