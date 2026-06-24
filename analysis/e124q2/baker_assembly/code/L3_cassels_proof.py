import math
# ============================================================
# PROVING (*) holds for ALL atoms a > N0: a <= 1 + sum(atoms < a).
#
# The atom set is A = {3^j : j>=2} U {4^j : j>=2} U {7^j : j>=2}.
# Sum of ALL atoms < x:  S(x) = sum_{3^j<x, j>=2} 3^j + (same for 4,7).
#   sum_{j>=2, 3^j<x} 3^j = (3^J - 9)/2 where 3^J is largest power of 3 below x
#                         ~ (3^{J})/2 ~ (largest 3-power below x)/2.
# In general S(x) ~ x/2 (3-ray) + x/3 (4-ray) + x/6 (7-ray) = x*(1/2+1/3+1/6) = x*beta = x*1.
# Wait: sum_{3^j < x} 3^j ~ x * (3/(3-1))... let me be exact.
#   The largest 3-power below x contributes ~x, and the geometric tail sums to
#   x/(1-1/3) = 1.5x for the 3-ray? NO -- sum of 3^j for 3^j<x is < x*3/2.
# Let me just bound: for the worst case, a is itself an atom (say a=3^J).
#   Atoms strictly below 3^J: all 3^j (j<J), all 4^j<3^J, all 7^j<3^J.
#   sum 3^j (2<=j<J) = (3^J-9)/2 ~ 3^J/2 = a/2.
#   sum 4^j (4^j<a): largest is < a, geometric => < a*4/3 ... actually
#     sum_{4^j < a} 4^j < (4/3)*(largest 4-power below a) < (4/3)*a.
#   Hmm that's already > a. Let me just compute the RATIO S(a)/a for atoms a.
# ============================================================
def S_below(x):
    s=0
    for base in (3,4,7):
        j=2
        while base**j < x:
            s+=base**j; j+=1
    return s

print("Ratio S(a-)/a for atoms a (sum of strictly-smaller atoms, over a):")
print("If this ratio >= 1 for all large atoms, (*) [a <= 1+S] holds forever.")
atoms=sorted(set([3**j for j in range(2,80)]+[4**j for j in range(2,80)]+[7**j for j in range(2,80)]))
worst=10
for a in atoms:
    if a < 4194304: continue
    if a > 10**30: break
    r = S_below(a)/a
    worst=min(worst,r)
    if a<10**12:
        print("  a=%-14d S(a-)/a = %.4f" % (a, r))
print()
print("Minimum ratio S(a-)/a over atoms a in (N0, 10^30):", "%.4f" % worst)
print()
# The ratio's liminf: by equidistribution, S(x)/x -> beta = 1 as x->inf (continuous),
# but at atoms a=base^J the ratio can DIP because a itself is large relative to S.
# The WORST case is when a is a power of the LARGEST base present below it with no
# other atom just below. Let me find the structural worst-case ratio analytically.
print("STRUCTURAL WORST CASE: a = base^J. The smaller atoms sum to:")
print("  3-ray below a: ~ (largest 3-power < a)/2 * (3/2)  [geometric 1+1/3+...]")
print("Let me compute liminf of S(a-)/a over ALL atoms exactly (to 7^60):")
worst_a=None; worst_r=10
for a in atoms:
    if a<=3982888: continue
    if a>7**60: break
    r=S_below(a)/a
    if r<worst_r: worst_r=r; worst_a=a
print("  liminf S(a-)/a = %.5f at a=%d=%s" % (worst_r, worst_a, 
      '3^%d'%round(math.log(worst_a,3)) if abs(3**round(math.log(worst_a,3))-worst_a)<1 else
      ('4^%d'%round(math.log(worst_a,4)) if abs(4**round(math.log(worst_a,4))-worst_a)<1 else
       '7^%d'%round(math.log(worst_a,7)))))
print()
print("If liminf > 1, then a <= S(a-) < 1+S(a-) for all large a => (*) HOLDS FOREVER,")
print("and L3 closes by window-propagation. Margin =", "%.4f" % (worst_r-1))
