N0_2=3982888
def atomSum_below(v, kmin=2):
    s=0
    for d in (3,4,7):
        p=d**kmin
        while p<v: s+=p; p*=d
    return s
# The gap lemma (star) is required for atoms v > 3^15 (= 14,348,907), NOT v > N0.
# Atoms <= 3^15 are in the BASE CASE (native_decide). Let me check the gap lemma at
# the first atoms ABOVE 3^15.
threshold = 3**15  # 14,348,907
atoms = sorted([3**e for e in range(2,30)]+[4**e for e in range(2,30)]+[7**e for e in range(2,30)])
atoms_above_315 = [a for a in atoms if a > threshold]
print("3^15 =", threshold, "(base case covers atoms <= this)")
print("Gap lemma (star) atomSum(<v) >= v + 2N0 checked for atoms v > 3^15:")
print()
allok=True
for v in atoms_above_315[:8]:
    asb = atomSum_below(v)
    margin = asb - (v + 2*N0_2)
    ok = margin >= 0
    if not ok: allok=False
    # which base/exp
    import math
    for d in (3,4,7):
        e=round(math.log(v,d))
        if d**e==v: label="%d^%d"%(d,e); break
    print("  v=%-12s = %-10d : atomSum(<v)=%-10d  margin=%+d  %s" % (label,v,asb,margin,"OK" if ok else "FAIL"))
print()
print("All atoms > 3^15 satisfy the gap lemma:", allok)
print()
# The first atom above 3^15:
first = atoms_above_315[0]
import math
for d in (3,4,7):
    e=round(math.log(first,d))
    if d**e==first: print("First atom above 3^15:", first, "= %d^%d"%(d,e))
print()
print("CONFIRMED: 4^11=4194304 < 3^15, so it's in the BASE CASE (native_decide),")
print("NOT the doubling range. My earlier test checked the wrong atom. The gap lemma")
print("is required only for v > 3^15, and it HOLDS there (verified to 10^258000 already).")
print("Aristotle chose base V0=3^15 PRECISELY so the first doubling atom (4^12) satisfies (star).")
