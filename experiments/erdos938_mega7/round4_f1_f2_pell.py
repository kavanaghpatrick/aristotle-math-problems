"""
Identify the underlying Pell structure of F1 (48, 49, 50) and F2 (182250, 182329, 182408).

F1: 48 = 2^4 * 3, 49 = 7^2, 50 = 2 * 5^2.
  Relation: 50 - 49 = 1, 49 - 48 = 1. So normalized is (48, 49, 50) = (49-1, 49, 49+1) i.e. just 49 with ±1.
  And 49 = 7^2. So this is the trivial Pell solution to x^2 - y^2 = ... well, (x-1)(x+1) = 48 * 50 = 2400.
  
  More structurally: (48*36, 49*36, 50*36) = (1728, 1764, 1800).
  48 = 2^4 * 3, so 48*36 = 2^4*3 * 2^2*3^2 = 2^6 * 3^3, powerful since each prime has power >= 2.
  50 = 2 * 5^2, so 50*36 = 2 * 5^2 * 4 * 9 = 2^3 * 3^2 * 5^2, powerful.
  
  Scaling by k^2: (48*k^2, 49*k^2, 50*k^2). For 48*k^2 = 2^4 * 3 * k^2 to be powerful, k must include 3 to odd power
  (to lift 3^1 to 3^{1+e}, need final exp >= 2 → e >= 1). So 3 | k.
  For 50*k^2 = 2 * 5^2 * k^2 powerful, k must include 2 to odd power. So 2 | k.
  Hence k = 6m. Triple = (48*36*m^2, 49*36*m^2, 50*36*m^2) = (1728*m^2, 1764*m^2, 1800*m^2).
  
  This is family parametrized by m, gap = 36*m^2. As m grows, gap grows quadratically.
  We saw only m=1, m=2 give consecutive APs.

F2: (182250, 182329, 182408).
  182250 = 2 * 3^6 * 5^3
  182329 = 427^2 (note 427 = 7 * 61, so 182329 = 7^2 * 61^2)
  182408 = 2^3 * 151^2
  Gap = 79. 2*182329 = 364658 = 182250 + 182408 ✓.
  
  Pell relation: 2 * 427^2 = 182250 + 182408 = 2 * 3^6 * 5^3 + 2^3 * 151^2.
  Divide by 2: 427^2 = 3^6 * 5^3 + 4 * 151^2.
  Let A = 3^3 * 5 = 135 (so 3^6 * 5^2 = 135^2 = 18225, and 3^6 * 5^3 = 18225 * 5 = 91125).
  Pell: 427^2 - 4 * 151^2 = 91125 = 3^6 * 5^3.
  Equivalent: 427^2 - (2*151)^2 = (427 - 302)(427 + 302) = 125 * 729 = 91125 = 5^3 * 3^6. ✓
  So 427 - 302 = 125 = 5^3, 427 + 302 = 729 = 3^6 = 27^2.
  
  This is FACTORING! 91125 = 5^3 * 3^6 is the product, and 5^3, 3^6 are the two cubes/sixth powers.
  
  KEY: 427 = (729 + 125)/2 = (3^6 + 5^3)/2 and 302 = (729 - 125)/2 = (3^6 - 5^3)/2.
  So the construction is: pick u, v such that uv is a perfect square AND u + v is even (so (u+v)/2 is integer)
  AND (u+v)/2 and (u-v)/2 produce the structure where:
    n0 = u * v (the middle * 2... wait)
  Let me re-do:
    n0 = 2 * u                         where u = 3^6 * 5^2 = 91125 ... no wait
    n0 = 182250 = 2 * 91125 = 2 * 5^3 * 3^6
    n1 = 182329 = 427^2 = ((729+125)/2)^2 = ((3^6 + 5^3)/2)^2
    n2 = 182408 = 8 * 22801 = 2^3 * 151^2
    
  So we have 729 - 125 = 604 = 2*302 = 2*2*151 = 4*151. And 4*151^2 = 91204 = 2^2 * 151^2.
  And n2 = 2*4*151^2 = 8*151^2 = 2 * (2*151)^2 = 2 * 604^2/... hmm
  n2 = 2^3 * 151^2 = 8 * 151^2 = 2 * (2*151)^2 / 2 ... let me just say n2 = 2 * (2*151)^2 = 2*604^2 / 2 = 302^2 * 2? 
  302^2 = 91204 = 2^2 * 151^2 = 4 * 151^2.
  So 2*302^2 = 8*151^2 = n2. ✓
  
  Similarly n0 = 2 * (3^3 * 5)^? Hmm 3^6 * 5^3 = (3^3 * 5)^2 * 5 = 135^2 * 5 = 91125. So n0 = 2*91125 = 2*135^2 * 5 = 270 * 135 * 5 = ...
  Or n0 = 2 * 5 * 135^2 = 10 * 135^2 = ... hmm need to think.

Cleaner: Set p = 3^3 = 27 (so p^2 = 729), q = 5 (so q^3 = 125, q*p^2 = 5*729 = 3645).
Then 729 + 125 = p^2 + q^3 = 854 → middle = 854 in primitive, but actually middle is 427 = 854/2.
And 729 - 125 = p^2 - q^3 = 604 = 2*302, with 302 = 2*151.

For this to work we need p^2 - q^3 to be EXACTLY 2 * 2 * (prime)^? i.e., have right form.

Let me PARAMETERIZE the family. We seek (a, b, c) where:
- a^2 - 343 b^2 = 2 (Pell-style, F2 with D=343/... no, F2 doesn't have D=343)
- Actually F2 has the relation (2 mid)^2 = n0 + n2 → 4 * middle^2 = n0 + n2.

Let me look at F2 normalized: n0=182250, n1=182329=427^2, n2=182408.
n0 + n2 = 2*427^2.
n0 = 2 * 91125 = 2 * 3^6 * 5^3
n2 = 8 * 151^2 = 2 * (2*151)^2 = 2 * 302^2

So 2 * 427^2 = 2 * 91125 + 2 * 302^2 → 427^2 = 91125 + 302^2 → 427^2 - 302^2 = 91125 = 3^6 * 5^3.

(427 - 302)(427 + 302) = 91125.
427 - 302 = 125 = 5^3.
427 + 302 = 729 = 3^6.

So PELL: u^2 - v^2 = w where u=427, v=302, w = 91125 = 5^3 * 3^6, and u-v = 5^3, u+v = 3^6.

So u = (5^3 + 3^6)/2 = (125 + 729)/2 = 854/2 = 427 ✓
   v = (3^6 - 5^3)/2 = (729-125)/2 = 604/2 = 302 ✓

This is NOT a Pell equation per se — it's a factorization!

Generalize: u^2 - v^2 = α^2k+1 * β^2m+1 with α = 5, k = 1 (so α^3), β = 3, m = ... wait.
3^6 is a perfect square AND a perfect cube (since 6 = 2*3). 5^3 is a perfect cube only.

So: u^2 - v^2 = A * B with A = 5^3 (cube), B = 3^6 (sixth power).
Then n0 = 2*A*B^{1/2}^2... hmm.

Look at n0 = 182250 = 2 * 5^3 * 3^6. So n0 = 2 * A * B where A * B = 5^3 * 3^6.
But that's not powerful by itself (2 has power 1)... wait it IS powerful since 5^3 and 3^6 are both >= squared.

Hmm wait, 2 appears to power 1 in n0 = 2 * 5^3 * 3^6. That would NOT be powerful!
But 182250 = 182250. Let me factor: 182250 / 2 = 91125 = 5^3 * 3^6 → 182250 = 2 * 5^3 * 3^6. YES, 2 has power 1.
So n0 is NOT powerful by itself!

But we said n0 was the first member of the F2 reduced AP triple. Let me re-verify.

Earlier output:
  "GCD=4, normalized: (182250, 182329, 182408)"

So 729000 / 4 = 182250 — but 182250 is NOT powerful. That's why we need a multiplier.
The actual smallest CONSECUTIVE AP IS (729000, 729316, 729632) — the m=1 case with k=2 scaling (k^2=4).
And we need k to contain enough '2's to make n0 powerful: k must be even, so k^2 has 2^{>=2}, lifting 2's power in n0 from 1 to >= 3.

Generalize family F2 parametrization: scale by k where k must be such that
   k^2 * (2 * 5^3 * 3^6, 427^2, 2 * 302^2)
are all powerful.

For k^2 * (2 * 5^3 * 3^6) powerful: 2 needs power >= 2 in k^2 * 2 * (5^3 * 3^6), so k must be even.
For k^2 * 427^2 = (427k)^2 powerful: always (perfect square).
For k^2 * (2 * 302^2): 302 = 2*151, so 2*302^2 = 2 * 4 * 151^2 = 8 * 151^2 = 2^3 * 151^2 (powerful by itself).
   k^2 * 2^3 * 151^2 is always powerful regardless of k.

So we need k EVEN. k = 2m. Then triple = (4m^2 * 182250, (427m * 2)^2 = 4*427^2 * m^2 = (854m)^2, 4m^2 * 182408).
For m=1: k=2, k^2=4, triple = (729000, 729316, 729632) ← AP3 ✓
For m=2: k=4, k^2=16, triple = (4*16*182250, 4*16*427^2, 4*16*182408)= (16*729000, 16*729316, ...) wait this is m=4 in old indexing.

Hmm let me redo. We had AP3-AP6 as scalings of (729000, 729316, 729632) by 1, 2, 4, 16.
That's NOT k^2 scaling, that's scaling by m directly. 

The scale-by-m direction: multiplying AP3 = (n0, n1, n2) by m gives (m*n0, m*n1, m*n2), an AP iff m is integer, all powerful iff... it depends on m's structure.

For m=2: 2 * 729000 = 1458000 = 2 * 2^3 * 3^6 * 5^3 = 2^4 * 3^6 * 5^3, powerful (each prime >= 2).
For m=3: 3 * 729000 = 2187000 = 2^3 * 3^7 * 5^3, powerful. 3*729316 = 2187948 = 4*546987 = ?
  3*729316: 729316 = 2^2 * 7^2 * 61^2. So 3*729316 = 2^2 * 3 * 7^2 * 61^2 — has 3 to power 1, NOT powerful.
For m=4: 4 * 729000 = 2916000 = 2^5 * 3^6 * 5^3, powerful. 4*729316 = 2^4 * 7^2 * 61^2, powerful. 4*729632 = 2^7 * 151^2, powerful. ✓
For m=8: 8 * 729000 = 2^6 * 3^6 * 5^3, powerful. 8*729316 = 2^5 * 7^2 * 61^2, powerful. 8*729632 = 2^8 * 151^2, powerful. ✓
For m=16: ALL powerful (just adds 2 powers).

So for any m where m absorbs into the existing prime factorizations, multiplication preserves powerful.

For consecutiveness, however, having all three powerful is necessary but not sufficient — we need no
other powerful in the interval.

Computational fact: m=1, 2, 4, 16 are consecutive. m=8 is not.

Theoretical explanation: when we scale by m=8, the gap becomes 8*316 = 2528, and the interval is 2528*2 = 5056.
For numbers near 5832000, density of powerful is ~0.36/sqrt(5.8e6) = 0.00015 per unit, so expected count in 5056-window is ~0.76.
There's exactly 1 intermediate powerful — it just happens to fall in the gap. By Poisson, this is a 33% probability event.

So heuristically, EACH SCALE m has some probability of having no intermediate powerful, and as m grows,
this probability stays ~ constant (around e^{-1.44} ~ 0.24).

This means F2 should produce INFINITELY MANY consecutive triples heuristically!
But proving this is exactly the open question.

CONCLUSION (Round 4):
- F1 and F2 are the only families up to 10^10.
- F2 = 2 * (3^6 + 5^3) decomposition. The "underlying Pell" is u^2 - v^2 = 5^3 * 3^6 with u-v=125, u+v=729.
- van Doorn family is x^2 - 7^3 y^2 = 2, distinct from F1/F2.
- The first van Doorn triple is NOT consecutive (5 intermediate powerfuls).
- Higher van Doorn solutions have x exponentially large, so consecutiveness check is computationally infeasible.
- Heuristically, both F2 and van Doorn families produce O(infinity) triples but only O(constant fraction)
  are consecutive — so each "family" potentially has infinitely many consecutive APs.

This SUPPORTS van Doorn's Conj 5: E938 is likely FALSE.
But it doesn't disprove E938 (would need explicit construction OR rigorous heuristic).
"""
print("Analysis complete.")
print()
print("Key findings:")
print(f"  F1 = (1728, 1764, 1800) family: middle 1764 = 42^2 = 49 * 36 (k=6, normalized base (48,49,50)).")
print(f"  F2 = (729000, 729316, 729632) family: middle 729316 = 854^2 = (427*2)^2 (with 4*427^2 - 4*4*151^2 = 4*91125 = 4*5^3*3^6).")
print(f"  van Doorn = ((x-2)^2, (x-1)^2, 7^3*y^2) with x^2 - 7^3*y^2 = 2. First solution: x=11427, y=617.")
print(f"  Up to N=10^10, the 6 consecutive APs are all in F1 (m=1, m=2) and F2 (m=1, m=2, m=4, m=16).")
print(f"  van Doorn's first triple at N ≈ 1.3e8 is NOT consecutive (5 intermediate powerfuls).")
