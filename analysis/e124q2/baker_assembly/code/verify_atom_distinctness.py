import math
# Aristotle's reduction (PROOF_NOTES line 12-14) assumes: "The atom values are pairwise
# distinct, so a subset sum is a genuine choice of distinct exponents per base."
# Verify NO two atoms 3^j, 4^k, 7^l (j,k,l >= 2) are equal. A collision would mean
# 3^j = 4^k (impossible, distinct primes) or 3^j = 7^l etc. Since 3,4=2^2,7 are
# multiplicatively independent in the relevant sense: 3^j=4^k => 3^j=2^{2k}, impossible
# for j,k>=1 (unique factorization). 3^j=7^l, 4^k=7^l likewise impossible. So distinctness
# is AUTOMATIC by unique factorization — no two atoms ever coincide. Confirm computationally
# in range and note the elementary proof.
print("Atom distinctness (Aristotle's standing assumption):")
print("  3^j = 4^k => 3^j = 2^{2k}: impossible (distinct primes 3,2), unique factorization.")
print("  3^j = 7^l: impossible (distinct primes 3,7).")
print("  4^k = 7^l => 2^{2k} = 7^l: impossible (distinct primes 2,7).")
print("  => ALL atoms pairwise distinct, ELEMENTARY (unique factorization). No range limit.")
print()
# computational sanity
atoms={}
collision=False
for base in (3,4,7):
    for e in range(2,200):
        v=base**e
        if v in atoms:
            print("  COLLISION:", v, "=",base,"^",e,"and",atoms[v]); collision=True
        else: atoms[v]=(base,e)
print("Computational check to exp 200:", "NO collisions" if not collision else "COLLISION FOUND")
print()
print("So the 'subset sum = distinct exponents per base' identity is rigorous and needs")
print("no hypothesis — it's free from unique factorization. One less thing to prove. ✓")
