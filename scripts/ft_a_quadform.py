#!/usr/bin/env python3
"""
Investigate: Why is A = q^2+q+1 always representable as x^2+9y^2 when q ≡ 71 (mod 72) and A is prime?

Key identity: A = N(q+1+ω) in Z[ω] where ω = e^{2πi/3}, so A = (q+1)^2 - (q+1) + 1.
Also: 4A = (2q+1)^2 + 3.

Plan:
1. Find all eligible (q, A) pairs
2. For each, find x,y with A = x^2 + 9y^2
3. Look for explicit formulas relating (x,y) to q
4. Prove theoretically via mod 3 argument on Gaussian representations
"""

from sympy import isprime
from math import isqrt
from collections import Counter

def find_rep_x2_9y2(n):
    """Find (x, y) with n = x^2 + 9*y^2, x >= 0, y > 0, or None."""
    max_y = isqrt(n // 9)
    for y in range(1, max_y + 1):
        rem = n - 9 * y * y
        if rem < 0:
            break
        if rem == 0:
            return (0, y)
        x = isqrt(rem)
        if x * x == rem:
            return (x, y)
    return None

def find_rep_x2_y2(n):
    """Find (s, t) with n = s^2 + t^2, s >= t > 0, or None."""
    for t in range(1, isqrt(n // 2) + 1):
        rem = n - t * t
        s = isqrt(rem)
        if s * s == rem and s >= t:
            return (s, t)
    return None

def find_rep_2x2_2xy_5y2(n):
    """Find (x, y) with n = 2x^2 + 2xy + 5y^2, or None."""
    max_y = isqrt(n // 5) + 1
    for y in range(-max_y, max_y + 1):
        # 2x^2 + 2yx + 5y^2 - n = 0
        # disc = 4y^2 - 8(5y^2 - n) = 4y^2 - 40y^2 + 8n = 8n - 36y^2
        disc = 8 * n - 36 * y * y
        if disc < 0:
            continue
        sd = isqrt(disc)
        if sd * sd == disc:
            for sign in [1, -1]:
                num = -2 * y + sign * sd
                if num % 4 == 0:
                    x = num // 4
                    val = 2*x*x + 2*x*y + 5*y*y
                    if val == n:
                        return (x, y)
    return None


print("=" * 80)
print("INVESTIGATION: A = q^2+q+1 representation as x^2+9y^2")
print("=" * 80)

# Phase 1: Find all eligible (q, A) pairs and their x^2+9y^2 representations
print("\n### Phase 1: Eligible primes and their representations ###\n")

eligible = []
for q in range(71, 100001, 72):
    A = q*q + q + 1
    if isprime(q) and isprime(A):
        rep = find_rep_x2_9y2(A)
        eligible.append((q, A, rep))

print(f"Found {len(eligible)} eligible (q, A) pairs with q < 100000\n")
print(f"{'q':>8} {'A':>16} {'x':>10} {'y':>6} {'s':>10} {'t':>6} {'s%3':>4} {'t%3':>4}")
print("-" * 80)

all_have_rep = True
for q, A, rep in eligible[:50]:
    if rep is None:
        all_have_rep = False
        tag = "NO REP!"
        print(f"{q:>8} {A:>16} {'???':>10} {'???':>6}")
    else:
        x, y = rep
        # Also find Gaussian representation
        g = find_rep_x2_y2(A)
        if g:
            s, t = g
            print(f"{q:>8} {A:>16} {x:>10} {y:>6} {s:>10} {t:>6} {s%3:>4} {t%3:>4}")
        else:
            print(f"{q:>8} {A:>16} {x:>10} {y:>6} {'?':>10} {'?':>6}")

print(f"\nAll {len(eligible)} pairs have x^2+9y^2 representation: {all_have_rep}")


# Phase 2: Look for patterns in (x, y) relative to q
print("\n\n### Phase 2: Relations between (x, y) and q ###\n")

for q, A, rep in eligible[:20]:
    if rep is None:
        continue
    x, y = rep
    print(f"q={q:>6}: A={A:>12}, x={x:>8}, y={y:>5}, "
          f"q-x={q-x:>8}, q-3y={q-3*y:>8}, "
          f"x+3y={x+3*y:>8}, x-3y={x-3*y:>8}, "
          f"gcd(x,q)={__import__('math').gcd(x,q):>3}, gcd(y,q)={__import__('math').gcd(y,q):>3}")


# Phase 3: THE SIMPLE PROOF via mod 3 argument
print("\n\n" + "=" * 80)
print("### THE PROOF (via Gaussian integers + mod 3) ###")
print("=" * 80)

print("""
THEOREM: If q ≡ 71 (mod 72), q prime, A = q^2+q+1 prime,
then A = x^2 + 9y^2 for some positive integers x, y.

PROOF:

Step 1: A ≡ 1 (mod 12).
  q ≡ -1 (mod 12), so q^2 ≡ 1, q ≡ -1 (mod 12).
  A = q^2+q+1 ≡ 1+(-1)+1 = 1 (mod 12).
  In particular A ≡ 1 (mod 4) and A ≡ 1 (mod 3).

Step 2: Gaussian two-square representation.
  A prime and A ≡ 1 (mod 4) implies A = s^2 + t^2 for unique s > t > 0
  (Fermat's theorem on sums of two squares).

Step 3: Mod 3 forces 3 | one component.
  Since A ≡ 1 (mod 3) and A = s^2 + t^2:
    s^2 + t^2 ≡ 1 (mod 3).
  Quadratic residues mod 3: {0, 1}. The only solutions to a+b ≡ 1 mod 3
  with a, b in {0, 1} are (a,b) = (0,1) or (1,0).
  So EXACTLY ONE of s^2, t^2 is ≡ 0 (mod 3), meaning exactly one of s, t is ≡ 0 (mod 3).
  (Both ≡ 0 would give A ≡ 0 mod 3, impossible since A is prime > 3.)

Step 4: Conclusion.
  Say 3 | t (WLOG). Write t = 3y. Then A = s^2 + 9y^2 with x := s.  QED.

COROLLARY: Every prime p ≡ 1 (mod 12) has the form x^2 + 9y^2.
  (p ≡ 1 mod 4 gives the two-square rep; p ≡ 1 mod 3 forces 3 | one component.)
""")


# Phase 4: Verify the corollary exhaustively
print("### Phase 4: Verify corollary for all primes p ≡ 1 mod 12 up to 100000 ###\n")

count_yes = 0
count_no = 0
counterexamples = []

for p in range(13, 100001):
    if not isprime(p) or p % 12 != 1:
        continue
    r = find_rep_x2_9y2(p)
    if r:
        count_yes += 1
    else:
        count_no += 1
        if len(counterexamples) < 5:
            counterexamples.append(p)
            # Debug: check Gaussian rep
            g = find_rep_x2_y2(p)
            if g:
                s, t = g
                print(f"  CLAIMED COUNTER: p={p} = {s}^2+{t}^2, s%3={s%3}, t%3={t%3}")
                # Check if we missed it
                if s % 3 == 0:
                    print(f"    Actually: p = {t}^2 + 9*{s//3}^2 — find_rep bug!")
                if t % 3 == 0:
                    print(f"    Actually: p = {s}^2 + 9*{t//3}^2 — find_rep bug!")

print(f"\nPrimes ≡ 1 mod 12 up to 100000:")
print(f"  Represented by x^2+9y^2: {count_yes}")
print(f"  NOT represented: {count_no}")
print(f"  Counterexamples: {counterexamples}")


# Phase 5: Genus theory — what does the other form represent?
print("\n\n### Phase 5: What primes does 2x^2+2xy+5y^2 represent? ###\n")

f2_primes = []
for p in range(2, 20001):
    if not isprime(p):
        continue
    r = find_rep_2x2_2xy_5y2(p)
    if r:
        f2_primes.append((p, r))

print(f"Primes represented by 2x^2+2xy+5y^2 up to 20000: {len(f2_primes)}")
print(f"First 30:")
for p, (x, y) in f2_primes[:30]:
    val = 2*x*x + 2*x*y + 5*y*y
    print(f"  p={p:>6} = 2*{x}^2+2*{x}*{y}+5*{y}^2 = {val}, p mod 12 = {p%12}, p mod 36 = {p%36}")

f2_mod12 = Counter(p % 12 for p, _ in f2_primes)
f2_mod36 = Counter(p % 36 for p, _ in f2_primes)
print(f"\n  p mod 12 distribution: {dict(f2_mod12)}")
print(f"  p mod 36 distribution: {dict(sorted(f2_mod36.items()))}")

# Also check f1
f1_mod36 = set()
for p in range(2, 20001):
    if not isprime(p):
        continue
    r = find_rep_x2_9y2(p)
    if r:
        f1_mod36.add(p % 36)

print(f"\n  x^2+9y^2 represents primes with p mod 36 in: {sorted(f1_mod36)}")
print(f"  2x^2+2xy+5y^2 represents primes with p mod 36 in: {sorted(set(p%36 for p,_ in f2_primes))}")

print("""
GENUS THEORY INTERPRETATION:
  Discriminant -36 = -4 * 9.
  The genus characters involve:
    - chi_{-4}(p) = (-1|p) = Legendre symbol = +1 iff p ≡ 1 mod 4
    - chi_9(p) related to (p|3) = +1 iff p ≡ 1 mod 3
  
  Genus 1 (x^2+9y^2): both characters = +1, i.e. p ≡ 1 mod 4 AND p ≡ 1 mod 3
    → p ≡ 1 mod 12
  Genus 2 (2x^2+2xy+5y^2): mixed characters
    → p in complementary residue classes

  Since h(-36) = 2 and there are 2 genera, each genus contains exactly 1 class.
  So p ≡ 1 mod 12 (with p prime > 3) ↔ p = x^2 + 9y^2.

  For A = q^2+q+1 with q ≡ 71 mod 72: A ≡ 1 mod 12, so A = x^2 + 9y^2. QED.
""")


# Phase 6: An even simpler proof — direct from norm
print("### Phase 6: Alternative proof via Eisenstein integers ###\n")

print("""
ALTERNATIVE PROOF (via Eisenstein integers, even more direct):

We know A = N_{Z[ω]}(q+1+ω) where N(a+bω) = a^2 - ab + b^2.

Key algebraic identity:
  a^2 - ab + b^2 = a^2 + b^2 - ab

For a = q+1, b = 1:
  A = (q+1)^2 - (q+1) + 1 = (q+1)^2 + 1 - (q+1) = q^2 + q + 1.  ✓

But this doesn't directly give x^2+9y^2. The Gaussian approach is cleaner:

CLEANEST PROOF:
  A ≡ 1 (mod 12) [Step 1 above].
  Any prime p ≡ 1 (mod 12) satisfies:
    (a) p ≡ 1 (mod 4) → p = s^2 + t^2 (Fermat)
    (b) p ≡ 1 (mod 3) → s^2 + t^2 ≡ 1 (mod 3) → exactly one of s,t ≡ 0 (mod 3)
    (c) Therefore p = x^2 + 9y^2.
  Three lines. No genus theory needed.  ∎
""")


# Phase 7: BUT WAIT — is this really right? h(-36) = 2 means NOT all primes ≡ 1 mod 12 should work...
# Let me very carefully recheck

print("### Phase 7: Careful recheck — potential issues ###\n")

print("The claim 'every prime p ≡ 1 mod 12 is x^2+9y^2' seems too strong.")
print("Standard reference: Cox, 'Primes of the form x^2+ny^2', Theorem 2.13.")
print("For n=9: p = x^2+9y^2 iff p ≡ 1 mod 3 and (-1|p) = 1, i.e., p ≡ 1 mod 12.")
print("Wait — Cox would say: if h(-4*9) = h(-36) = 2 and there's 1 form per genus,")
print("then representation is determined by genus characters alone.")
print("Genus characters for D=-36: the conditions ARE p ≡ 1 mod 4 and p ≡ 1 mod 3.")
print("So YES: p ≡ 1 mod 12 ↔ p = x^2 + 9y^2 (for primes p > 3).")
print()
print("This is consistent because when h = number of genera (here h=2, genera=2),")
print("each genus has exactly one class, so genus characters COMPLETELY determine")
print("which form represents which primes. No additional conditions needed.")
print()
print("Compare with x^2+27y^2: disc = -108 = -4*27. h(-108) = 3.")
print("Number of genera for -108: 2 (since -108 = -4 * 27 = -4 * 3^3).")
print("So 3 classes in 2 genera → genus theory alone does NOT suffice.")
print("That's why x^2+27y^2 needs the additional cubic residue condition.")
print()

# Double-check h(-36) = 2
print("Verification: class number h(-36) via direct form enumeration:")
# Reduced forms of discriminant -36:
# Form ax^2+bxy+cy^2 with b^2-4ac = -36, |b| <= a <= c, b >= 0 if |b|=a or a=c
# b^2 + 36 = 4ac. b even since disc ≡ 0 mod 4: b = 0, 2, 4, 6...
# b=0: 4ac = 36, ac = 9. (a,c) with a <= c: (1,9), (3,3).
#   (1,0,9): x^2+9y^2. Reduced? |0|=0 <= 1 ≤ 9. Yes.
#   (3,0,3): 3x^2+3y^2. Reduced? |0|=0 <= 3 = 3. Yes. But gcd(3,0,3)=3, so it's not primitive!
# b=2: 4+36 = 40 = 4ac, ac=10. a <= c, |b|=2 <= a. a >= 2. (2,5): form 2x^2+2xy+5y^2. Reduced? 2<=2<=5. Yes.
#   (5,2,2): would need |2|<=5<=2, fails a<=c.
# b=4: 16+36=52=4ac, ac=13. a >= 4, a<=c: (13, but 13>4... no): 4<=c, ac=13 impossible with a>=4.
# b=6: 36+36=72=4ac, ac=18. a>=6, a<=c: no solution.
# So primitive reduced forms: {(1,0,9)} and {(2,1,5)} → h(-36) = 2. ✓
print("Reduced primitive forms of disc -36:")
print("  (1,0,9): x^2+9y^2")
print("  (2,1,5): 2x^2+2xy+5y^2   [b=2 not 1, but the standard form uses b even for even disc]")
print("  h(-36) = 2 ✓")
print()

# Count genera
print("Number of genera: For D = -36 = -4 * 9:")
print("  D = -4 * 9 = -2^2 * 3^2")
print("  The genus characters for negative D:")
print("  Since D = -36 and |D| = 36 = 4 * 9:")
print("  - Factor -36 = (-4)(9) or (-36)(1)")
print("  - Number of genera = 2^(t-1) where t = number of 'genus characters'")
print("  - For D = -36: t = 2 (characters for -4 and for 9), so genera = 2^(2-1) = 2")
print("  - Since h = 2 = number of genera, EACH genus has exactly ONE class.")
print("  - Therefore genus theory COMPLETELY determines representation. ✓")
print()

print("=" * 80)
print("FINAL ANSWER")
print("=" * 80)
print("""
THEOREM: Let q be a prime with q ≡ 71 (mod 72), and let A = q^2+q+1 be prime.
Then A = x^2 + 9y^2 for some positive integers x, y.

PROOF: Three steps.

(1) A ≡ 1 (mod 12).
    Since q ≡ -1 (mod 12): A = q^2+q+1 ≡ 1-1+1 = 1 (mod 12).

(2) A = s^2 + t^2 with exactly one of s, t divisible by 3.
    Since A ≡ 1 (mod 4), Fermat's two-square theorem gives A = s^2 + t^2.
    Since A ≡ 1 (mod 3): s^2 + t^2 ≡ 1 (mod 3). As {0^2, 1^2, 2^2} ≡ {0, 1, 1} mod 3,
    the equation a + b = 1 (mod 3) with a, b ∈ {0, 1} forces {a,b} = {0, 1}.
    So exactly one of s, t is divisible by 3.

(3) Write t = 3y (or s = 3y). Then A = x^2 + 9y^2.  ∎

NOTE: This proves the stronger result that EVERY prime p ≡ 1 (mod 12) is x^2+9y^2.
This is a classical fact equivalent to: disc(-36) has class number 2 = number of genera,
so genus characters (which are just the conditions p ≡ 1 mod 4 and p ≡ 1 mod 3)
completely determine the representing form.
""")
