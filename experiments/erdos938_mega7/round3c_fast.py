"""
Faster approach. 343 = 7^3.
x^2 - 7^3 y^2 = 2  is equivalent to  x^2 - 7*(7y)^2 = 2 ... but 7 is not in standard Pell form for ax^2-by^2=c.
Or use x^2 - 343*y^2 = 2 directly.

Continued fraction of sqrt(343) = sqrt(343) ≈ 18.520...
Use the standard Pell-equation algorithm.
"""
import math
from math import gcd, isqrt
from fractions import Fraction

def pell_fundamental(D):
    """Fundamental solution of x^2 - D*y^2 = 1 via continued fraction expansion of sqrt(D)."""
    m, d, a0 = 0, 1, isqrt(D)
    a = a0
    p_prev, p = 1, a
    q_prev, q = 0, 1
    while True:
        m = d * a - m
        d = (D - m*m) // d
        a = (a0 + m) // d
        if d == 1 and p*p - D*q*q == 1:
            return (p, q)
        p_prev, p = p, a*p + p_prev
        q_prev, q = q, a*q + q_prev

print(f"Fundamental for x^2 - 343*y^2 = 1:")
a, b = pell_fundamental(343)
print(f"  a={a}, b={b}")
print(f"  Verify: {a**2 - 343*b**2}")

# Now van Doorn's equation: x^2 - 343 y^2 = 2.
# Need to find all "primitive" solutions modulo orbit of (a, b).
# Primitive: (11427, 617) is one.
# Are there others? We can search small y.
print("\nSearching small (x, y) with x^2 - 343*y^2 = 2:")
sols0 = []
for y in range(1, 200000):
    rhs = 343*y*y + 2
    x = isqrt(rhs)
    if x*x == rhs:
        sols0.append((x, y))
        print(f"  x={x}, y={y}")
        if len(sols0) >= 4:
            break

# Generate higher solutions from (11427, 617) using (a, b)
print(f"\nGenerating higher solutions from (11427, 617) with multiplier (a={a}, b={b}):")
x0, y0 = 11427, 617
for i in range(6):
    print(f"  Sol {i}: x={x0:,}, y={y0:,}, x^2 - 343y^2 = {x0**2 - 343*y0**2}")
    nx = a*x0 + 343*b*y0
    ny = a*y0 + b*x0
    x0, y0 = nx, ny

# Also try other orbits: maybe (x, -y) or (-x, y) trick gives a 2nd primitive class.
print("\n--- Triple analysis for each (x, y) in van Doorn family ---")
print("Triple structure: ((x-2)^2, (x-1)^2, 343*y^2)")
print("(x-1)^2 - (x-2)^2 = 2x-3 = gap")
print("343*y^2 - (x-1)^2 = 2 - 1 = ... wait x^2 - 343y^2 = 2 → 343y^2 = x^2 - 2 = (x-1)(x+1) - 1")
print("Hmm let me reconsider.")
print()

# Direct: 343y^2 - (x-1)^2 = x^2 - 2 - (x-1)^2 = x^2 - 2 - x^2 + 2x - 1 = 2x - 3.
# And (x-1)^2 - (x-2)^2 = 2x - 3.
# So both gaps are 2x - 3. The triple is indeed an AP.

# So gap = 2x - 3 for each solution. As x grows, gap grows linearly.
# For consecutiveness, we need NO powerful in (n0, n2) except n1 = (x-1)^2.
# The interval (n0, n2) has width 2(2x-3) ≈ 4x.

# For x = 11427: width ≈ 45,708 around n0 ≈ 1.3e8. Density of powerful is ~ √n, so ~12 powerful per interval of size 45,708 around 1.3e8.
# Indeed 5 intermediate powerfuls were found earlier.

# For larger x (next solution), gap is 4x ≈ huge. Density of powerful in (n0, n2) ≈ (n2-n0)/sqrt(n_avg) * const.
# (n2-n0)/sqrt(n0) ≈ 4x / x = 4. So ~4 powerful expected per interval, regardless of x.
# This means LARGE van Doorn solutions are EXPECTED to have multiple intervening powerfuls — never consecutive!

# Asymptotic heuristic:
# - n0 = (x-2)^2 ≈ x^2
# - width = 2(2x-3) ≈ 4x
# - density of powerful near n is ~ (ζ(3/2) - 1) / (2*sqrt(n)) ≈ 0.36 / sqrt(n) ≈ 0.36 / x
# - expected count in (n0, n2) ≈ 4x * 0.36/x = 1.44
# - so ~ 1.4 expected powerfuls per interval, suggesting ~ 25% of solutions have 0 intermediate (=consecutive)

# But this is just heuristic. The Pell solutions grow exponentially: x_n ~ (a + b√343)^n.
# Each solution has indep ~25% chance of consecutive by Poisson heuristic.
# Sum over infinite solutions: expected number consecutive = ∞? Or do correlations matter?

# Actually for x going to infinity with constant ~1.44 expected count of intermediates,
# Pr(no intermediate) ≈ e^{-1.44} ≈ 0.24, so ~24% of Pell solutions should be consecutive,
# giving INFINITELY MANY consecutive triples — DISPROVING E938!

# But this is the heuristic that van Doorn states. The QUESTION is whether the Pell-solution
# values systematically AVOID having intervening powerfuls (correlations from algebraic structure)
# or whether the heuristic holds.

