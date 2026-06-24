# Reconcile the two S(a-) computations. The discrepancy: does S(a-) include
# the SAME-base smaller powers or not?
def S_below_v1(a):  # earlier version
    s=0
    for b in (3,4,7):
        p=b*b
        while p<a: s+=p; p*=b
    return s

a = 4**11  # 4194304
print("a = 4^11 =", a)
print("S_below_v1(a) =", S_below_v1(a), " a - S =", a - S_below_v1(a))
# manually: atoms below 4194304:
import itertools
atoms_below = sorted([3**j for j in range(2,20) if 3**j < a] + 
                     [4**j for j in range(2,20) if 4**j < a] +
                     [7**j for j in range(2,20) if 7**j < a])
print("atoms below a:", atoms_below)
print("sum =", sum(atoms_below), " a - sum =", a - sum(atoms_below))
print()
# So at 4^11, a - S = -556064 (S > a). But Brown's LAST violation was at index 113
# (atom ~9e32). Let me look at THAT atom specifically.
a2 = 909543680129861140820205019889143
print("Brown's last-violation atom a2 =", a2)
import math
for b in (3,4,7):
    e = round(math.log(a2,b))
    if b**e==a2: print("  a2 =", b,"^",e)
print("S_below_v1(a2) =", S_below_v1(a2))
print("a2 - 1 - S(a2-) =", a2 - 1 - S_below_v1(a2))
print()
# Is a2 - S really > 0 here? That contradicts 'S(a-)>a always'. Check:
print("a2 > S(a2-)?", a2 > S_below_v1(a2), " => S(a-) > a FAILS at a2")
print()
print("RESOLUTION: S(a-) > a holds for SMALL atoms (4^11) but FAILS for large ones")
print("like a2~9e32. Let me find WHERE S(a-)/a first drops below 1 (if it does):")
allat=sorted(set([3**j for j in range(2,80)]+[4**j for j in range(2,80)]+[7**j for j in range(2,80)]))
for a in allat:
    if a>10**40: break
    r = S_below_v1(a)/a
    if r < 1.0:
        print("  S(a-)/a < 1 first at a=%.3e, ratio=%.4f" % (a, r))
        break
else:
    print("  S(a-)/a >= 1 for all atoms to 10^40")
# print the ratio trend for large atoms
print()
print("Ratio S(a-)/a for the largest atoms checked:")
for a in allat[-8:]:
    if a<10**40:
        print("  a=%.3e ratio=%.5f" % (a, S_below_v1(a)/a))
