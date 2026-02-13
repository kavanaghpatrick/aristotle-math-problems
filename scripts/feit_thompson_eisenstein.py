#!/usr/bin/env python3
"""
Feit-Thompson p=3 conjecture: Eisenstein integer analysis for q ≡ 71 (mod 72).

SETUP:
  q prime, q ≡ 2 mod 3, A = q² + q + 1 = Φ₃(q) prime.
  Want to show: 3^q ≢ 1 (mod A).

In the Eisenstein integers Z[ω] where ω = e^{2πi/3}:
  - A = (q - ω)(q - ω²) = π · π̄  where π = q - ω
  - Z[ω]/(π) ≅ F_A
  - ω ≡ q (mod π)

We analyze the cubic residue symbol (3/π)₃ in Z[ω].
"""

import sympy
from sympy import isprime, nextprime
from typing import Tuple, Optional
import sys

# ============================================================
# Part 1: Eisenstein integer arithmetic
# ============================================================

class Eisenstein:
    """
    Represents a + b*ω where ω = e^{2πi/3}, ω² + ω + 1 = 0.
    Multiplication: (a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω
    Norm: N(a + bω) = a² - ab + b²
    """
    def __init__(self, a: int, b: int):
        self.a = a
        self.b = b

    def __repr__(self):
        if self.b == 0:
            return f"{self.a}"
        elif self.a == 0:
            return f"{self.b}ω"
        else:
            sign = "+" if self.b > 0 else "-"
            return f"({self.a} {sign} {abs(self.b)}ω)"

    def __add__(self, other):
        if isinstance(other, int):
            return Eisenstein(self.a + other, self.b)
        return Eisenstein(self.a + other.a, self.b + other.b)

    def __radd__(self, other):
        if isinstance(other, int):
            return Eisenstein(self.a + other, self.b)
        return NotImplemented

    def __sub__(self, other):
        if isinstance(other, int):
            return Eisenstein(self.a - other, self.b)
        return Eisenstein(self.a - other.a, self.b - other.b)

    def __rsub__(self, other):
        if isinstance(other, int):
            return Eisenstein(other - self.a, -self.b)
        return NotImplemented

    def __neg__(self):
        return Eisenstein(-self.a, -self.b)

    def __mul__(self, other):
        if isinstance(other, int):
            return Eisenstein(self.a * other, self.b * other)
        # (a + bω)(c + dω) = ac + adω + bcω + bdω²
        # = ac + adω + bcω + bd(-1 - ω)
        # = (ac - bd) + (ad + bc - bd)ω
        a, b = self.a, self.b
        c, d = other.a, other.b
        return Eisenstein(a*c - b*d, a*d + b*c - b*d)

    def __rmul__(self, other):
        if isinstance(other, int):
            return Eisenstein(self.a * other, self.b * other)
        return NotImplemented

    def __eq__(self, other):
        if isinstance(other, int):
            return self.a == other and self.b == 0
        return self.a == other.a and self.b == other.b

    def norm(self) -> int:
        """N(a + bω) = a² - ab + b²"""
        return self.a**2 - self.a*self.b + self.b**2

    def conj(self):
        """Conjugate: a + bω → a + bω² = a + b(-1-ω) = (a-b) + (-b)ω"""
        return Eisenstein(self.a - self.b, -self.b)

    def mod(self, m):
        """Reduce mod integer m (component-wise)."""
        return Eisenstein(self.a % m, self.b % m)


# Standard elements
OMEGA = Eisenstein(0, 1)      # ω
OMEGA2 = Eisenstein(-1, -1)   # ω² = -1 - ω
ONE = Eisenstein(1, 0)
ZERO = Eisenstein(0, 0)
UNITS = [ONE, -ONE, OMEGA, -OMEGA, OMEGA2, -OMEGA2]  # All 6 units

def eisenstein_mod_reduce(z: Eisenstein, pi: Eisenstein) -> Eisenstein:
    """
    Reduce z modulo pi in Z[ω].
    Uses the fact that Z[ω]/(π) ≅ Z/N(π)Z when π is prime.

    For our case: π = q - ω, ω ≡ q mod π.
    So a + bω ≡ a + bq ≡ (a + bq) mod A in F_A.
    """
    # This is the naive approach; we'll use the explicit isomorphism
    pass

def eisenstein_to_int_mod_pi(z: Eisenstein, q: int, A: int) -> int:
    """
    Map z = a + bω to an integer mod A, using ω ≡ q (mod π).
    """
    return (z.a + z.b * q) % A

def int_to_eisenstein_mod_pi(n: int, q: int, A: int) -> int:
    """Just return n mod A (the integer representative in F_A)."""
    return n % A


# ============================================================
# Part 2: Cubic residue symbol computation
# ============================================================

def cubic_residue_symbol_direct(alpha_int: int, A: int) -> int:
    """
    Compute (alpha / pi)_3 directly:
    α^{(A-1)/3} mod A, then map to {0, 1, ω, ω²} ↔ {0, 1, q, q²}.

    Returns: 0 if α ≡ 0, 1 if cube, q if (alpha/pi)_3 = ω, q² (mod A) if ω².
    Actually returns the power of ω: 0, 1, 2 (or -1 for 0).
    """
    if alpha_int % A == 0:
        return -1  # zero

    exp = (A - 1) // 3
    result = pow(alpha_int, exp, A)

    q_val = None
    # Find q from A = q² + q + 1
    # q is the positive root of q² + q + 1 - A = 0
    import math
    disc = 1 - 4*(1 - A)
    q_val = (-1 + int(math.isqrt(disc))) // 2

    q_mod = q_val % A
    q2_mod = pow(q_val, 2, A)

    if result == 1:
        return 0  # ω^0 = 1
    elif result == q_mod:
        return 1  # ω^1
    elif result == q2_mod:
        return 2  # ω^2
    else:
        # Shouldn't happen
        return None


def verify_factorization_of_3(q: int) -> dict:
    """
    Verify: 3 = -ω²(1-ω)² in Z[ω].

    (1-ω)² = 1 - 2ω + ω² = 1 - 2ω + (-1-ω) = -3ω
    -ω² · (-3ω) = -ω² · (-3ω) = 3ω³ = 3·1 = 3. ✓

    Wait let me redo:
    (1-ω) = 1 - ω
    (1-ω)² = 1 - 2ω + ω² = 1 - 2ω + (-1-ω) = -3ω
    -ω² · (1-ω)² = -ω² · (-3ω) = 3ω³ = 3 ✓
    """
    one_minus_omega = ONE - OMEGA  # (1, -1) = 1 - ω
    sq = one_minus_omega * one_minus_omega
    # sq should be -3ω = (0, -3)

    neg_omega2 = -OMEGA2  # -(−1−ω) = (1, 1) = 1 + ω
    product = neg_omega2 * sq

    return {
        '1-ω': one_minus_omega,
        '(1-ω)²': sq,
        '-ω²': neg_omega2,
        '-ω²·(1-ω)²': product,
        'equals_3': product == Eisenstein(3, 0)
    }


def make_primary(pi: Eisenstein) -> Tuple[Eisenstein, Eisenstein]:
    """
    Find unit u such that u·π is primary.
    Primary means: a + bω with a ≡ 2 mod 3 (i.e., a ≡ -1 mod 3) and b ≡ 0 mod 3.

    Returns (u, u·π) where u is a unit.
    """
    for u in UNITS:
        candidate = u * pi
        if candidate.a % 3 == 2 and candidate.b % 3 == 0:
            return (u, candidate)
    # Also try: primary can mean a ≡ -1 mod 3, b ≡ 0 mod 3
    # Different references use different conventions. Let's check both.
    for u in UNITS:
        candidate = u * pi
        # Ireland-Rosen convention: a ≡ 2 mod 3, b ≡ 0 mod 3
        if candidate.a % 3 == 2 and candidate.b % 3 == 0:
            return (u, candidate)
    return (None, None)


def cubic_supplement(pi0: Eisenstein) -> int:
    """
    For primary π₀ = a + bω (a ≡ 2 mod 3, b ≡ 0 mod 3):

    ((1-ω)/π₀)₃ = ω^{(a-1)/3 + b/3}   [Ireland-Rosen, Lemma 9.6.3]

    Wait — there are different formulas in the literature. Let me use the
    standard one from Ireland-Rosen Chapter 9:

    For primary π = a + bω:
      (ω/π)₃ = ω^{(N(π)-1)/3} ... no, that's for Legendre-like.

    Actually the supplement laws are:
      (ω/π)₃ = ω^{(a-1+b)/3}      ... hmm, let me just compute directly.

    We'll compute directly via the definition: ((1-ω)/π₀)₃ = (1-ω)^{(N(π₀)-1)/3} mod π₀.
    """
    # Direct computation is better. We work in Z/AZ using ω ≡ q.
    pass


# ============================================================
# Part 3: Main verification for q ≡ 71 (mod 72)
# ============================================================

def find_primes_q_mod_72(n_primes: int = 30) -> list:
    """Find primes q with q ≡ 71 mod 72 and A = q²+q+1 also prime."""
    results = []
    q = 71
    while len(results) < n_primes:
        if isprime(q):
            A = q*q + q + 1
            if isprime(A):
                results.append((q, A))
        q += 72
    return results


def full_analysis(q: int, A: int, verbose: bool = True) -> dict:
    """
    Complete analysis for one (q, A) pair.
    """
    result = {}

    if verbose:
        print(f"\n{'='*70}")
        print(f"q = {q}, A = q²+q+1 = {A}")
        print(f"q mod 3 = {q%3}, q mod 8 = {q%8}, q mod 9 = {q%9}, q mod 72 = {q%72}")
        print(f"(A-1)/3 = {(A-1)//3}")

    # --- Basic check: 3^q mod A ---
    three_q = pow(3, q, A)
    result['3^q_mod_A'] = three_q
    result['consistent'] = (three_q == 1)
    if verbose:
        print(f"\n3^q mod A = {three_q}")
        print(f"3^q ≡ 1 (mod A)? {'YES — CONSISTENT (bad for us)' if three_q == 1 else 'NO — CONTRADICTION (good!)'}")

    if three_q == 1:
        if verbose:
            print("  *** 3^q ≡ 1 mod A! The cubic residue approach must find a deeper contradiction. ***")

    # --- Cubic residue of 3 mod A ---
    exp = (A - 1) // 3
    three_exp = pow(3, exp, A)
    q_mod = q % A
    q2_mod = pow(q, 2, A)

    result['3^{(A-1)/3}_mod_A'] = three_exp
    result['q_mod_A'] = q_mod
    result['q^2_mod_A'] = q2_mod

    if three_exp == 1:
        chi3 = 0  # (3/π)₃ = ω^0 = 1 → 3 is a cubic residue
    elif three_exp == q_mod:
        chi3 = 1  # (3/π)₃ = ω
    elif three_exp == q2_mod:
        chi3 = 2  # (3/π)₃ = ω²
    else:
        chi3 = None

    result['chi3'] = chi3

    if verbose:
        print(f"\nCubic residue symbol (3/π)₃:")
        print(f"  3^{{(A-1)/3}} mod A = {three_exp}")
        print(f"  q mod A = {q_mod}")
        print(f"  q² mod A = {q2_mod}")
        labels = {0: '1 (cubic residue)', 1: 'ω (not CR)', 2: 'ω² (not CR)', None: 'ERROR'}
        print(f"  (3/π)₃ = ω^{chi3} = {labels[chi3]}")

    # --- If 3^q ≡ 1 mod A, what does this imply for (3/π)₃? ---
    # 3^q ≡ 1 mod A means 3 has multiplicative order dividing q mod A.
    # |F_A*| = A-1 = q² + q = q(q+1).
    # ord(3) | q. Also ord(3) | q(q+1).
    # Since q is prime, ord(3) ∈ {1, q}.
    # 3 ≡ 1 mod A? Only if A | 2, impossible. So ord(3) = q.
    # Then (3/π)₃ = 3^{(A-1)/3} = 3^{q(q+1)/3}.
    # Since 3^q ≡ 1: 3^{q(q+1)/3} = (3^q)^{(q+1)/3} = 1^{(q+1)/3} = 1.
    # So if 3^q ≡ 1, then (3/π)₃ = 1 NECESSARILY.

    if verbose:
        print(f"\n  Note: if 3^q ≡ 1 (mod A), then (3/π)₃ = 1 necessarily.")
        print(f"  Proof: (A-1)/3 = q(q+1)/3, and 3^q ≡ 1 ⟹ 3^{{q(q+1)/3}} = 1^{{(q+1)/3}} = 1")
        if three_q == 1 and chi3 != 0:
            print(f"  *** INCONSISTENCY! 3^q = 1 but (3/π)₃ ≠ 1. BUG in computation! ***")
        elif three_q != 1 and chi3 == 0:
            print(f"  But here 3^q ≠ 1, yet (3/π)₃ = 1. So 3 is a CR but not a q-th power.")

    # --- Primary form of π ---
    pi = Eisenstein(q, -1)  # q - ω
    u, pi0 = make_primary(pi)
    result['pi'] = pi
    result['pi0'] = pi0
    result['unit'] = u

    if verbose:
        print(f"\nPrimary form:")
        print(f"  π = q - ω = {pi}, N(π) = {pi.norm()}")
        print(f"  Unit u = {u}")
        print(f"  π₀ = u·π = {pi0}, N(π₀) = {pi0.norm()}")
        if pi0:
            print(f"  π₀ = {pi0.a} + {pi0.b}ω")
            print(f"  a mod 3 = {pi0.a % 3}, b mod 3 = {pi0.b % 3}")

    # --- Verify the user's claim: π₀ = -ω·π = -1 - (q+1)ω ---
    neg_omega_pi = (-OMEGA) * pi
    if verbose:
        print(f"\n  -ω·π = {neg_omega_pi}")
        expected = Eisenstein(-1, -(q+1))
        print(f"  Expected: -1 - (q+1)ω = {expected}")
        print(f"  Match: {neg_omega_pi == expected}")

    # --- Cubic supplement: ((1-ω)/π₀)₃ computed directly ---
    if pi0:
        # (1-ω) mod π means (1-q) mod A in the residue field
        one_minus_omega_int = (1 - q) % A
        supplement_val = pow(one_minus_omega_int, exp, A)

        if supplement_val == 1:
            supp_power = 0
        elif supplement_val == q_mod:
            supp_power = 1
        elif supplement_val == q2_mod:
            supp_power = 2
        else:
            supp_power = None

        result['supplement_direct'] = supp_power

        if verbose:
            print(f"\nCubic supplement ((1-ω)/π₀)₃ — direct computation:")
            print(f"  (1-ω) mod π ↔ (1-q) mod A = {one_minus_omega_int}")
            print(f"  (1-q)^{{(A-1)/3}} mod A = {supplement_val}")
            print(f"  ((1-ω)/π)₃ = ω^{supp_power}")

        # User's formula: ((1-ω)/π₀)₃ = ω^{(q+1)/3} for q ≡ 8 mod 9
        if q % 9 == 8:
            user_prediction = ((q + 1) // 3) % 3
            if verbose:
                print(f"\n  User's formula prediction: ω^{{(q+1)/3 mod 3}} = ω^{user_prediction}")
                print(f"    (q+1)/3 = {(q+1)//3}, mod 3 = {user_prediction}")

            # BUT: the supplement is for π₀ = -ω·π, not π directly.
            # (1-ω)/π₀ vs (1-ω)/π differ by the unit factor.
            # Actually the cubic residue symbol (α/π₀)₃ uses π₀, so
            # we need (1-ω) mod π₀. But Z[ω]/(π) = Z[ω]/(π₀) since they're associates.
            # The cubic residue symbol IS THE SAME for associates? NO!
            # (α/uπ)₃ = (α/π)₃ · (α/u)₃ ... but u is a unit.
            # Actually (α/π)₃ depends on π, not just the ideal (π).
            # The cubic residue CHARACTER χ_π is well-defined by the ideal,
            # but the symbol (·/π)₃ as defined by Eisenstein depends on the specific generator.
            # For PRIMARY π₀: (α/π₀)₃ is the "canonical" symbol.
            # The supplement formulas apply to PRIMARY generators.
            #
            # So: our direct computation of (1-ω)^{(A-1)/3} mod A gives (α/π)₃
            # where the "mod A" computation works because Z[ω]/(π) ≅ F_A via ω ↦ q.
            # But this is (α/π)₃, NOT (α/π₀)₃.
            #
            # Actually wait: the cubic residue symbol α^{(Nπ-1)/3} mod π
            # doesn't depend on the generator — it depends only on the ideal!
            # α^{(A-1)/3} mod π is computed entirely in Z[ω]/(π) = F_A.
            # So (α/π)₃ = (α/π₀)₃. The symbol depends on the ideal, not the generator.
            #
            # The RECIPROCITY LAW and SUPPLEMENT formulas are stated for primary elements,
            # but the symbol itself is ideal-theoretic.

            if verbose:
                print(f"\n  Note: (α/π)₃ = (α/π₀)₃ — symbol depends on ideal, not generator.")
                print(f"  Direct match: {supp_power == user_prediction}")

    # --- Now decompose (3/π)₃ via 3 = -ω²(1-ω)² ---
    if verbose:
        print(f"\nDecomposition of (3/π)₃ via 3 = -ω²(1-ω)²:")

    # (3/π)₃ = (-ω²/π)₃ · ((1-ω)²/π)₃ = (-ω²/π)₃ · ((1-ω)/π)₃²

    # (-ω²/π)₃ = (-1/π)₃ · (ω²/π)₃ = (-1/π)₃ · (ω/π)₃²

    # Direct computation of each factor:
    neg1_int = (-1) % A
    omega_int = q % A  # ω ≡ q mod π
    omega2_int = pow(q, 2, A)  # ω² ≡ q² mod π
    neg_omega2_int = (-omega2_int) % A  # -ω² mod A
    one_minus_omega_int = (1 - q) % A
    three_int = 3 % A

    # Compute each symbol
    neg1_symbol_val = pow(neg1_int, exp, A)
    omega_symbol_val = pow(omega_int, exp, A)
    omega2_symbol_val = pow(omega2_int, exp, A)
    neg_omega2_symbol_val = pow(neg_omega2_int, exp, A)
    one_minus_omega_symbol_val = pow(one_minus_omega_int, exp, A)
    three_symbol_val = pow(three_int, exp, A)

    def to_power(val, q, A):
        q_mod = q % A
        q2_mod = pow(q, 2, A)
        if val == 1: return 0
        if val == q_mod: return 1
        if val == q2_mod: return 2
        return None

    p_neg1 = to_power(neg1_symbol_val, q, A)
    p_omega = to_power(omega_symbol_val, q, A)
    p_omega2 = to_power(omega2_symbol_val, q, A)
    p_neg_omega2 = to_power(neg_omega2_symbol_val, q, A)
    p_1mw = to_power(one_minus_omega_symbol_val, q, A)
    p_3 = to_power(three_symbol_val, q, A)

    result['(-1/π)₃'] = p_neg1
    result['(ω/π)₃'] = p_omega
    result['(ω²/π)₃'] = p_omega2
    result['(-ω²/π)₃'] = p_neg_omega2
    result['((1-ω)/π)₃'] = p_1mw
    result['(3/π)₃'] = p_3

    if verbose:
        print(f"  (-1)^{{(A-1)/3}} mod A = {neg1_symbol_val}  →  (-1/π)₃ = ω^{p_neg1}")
        print(f"  ω^{{(A-1)/3}} = q^{{(A-1)/3}} mod A = {omega_symbol_val}  →  (ω/π)₃ = ω^{p_omega}")
        print(f"  (ω²/π)₃ = (ω/π)₃² = ω^{(2*p_omega)%3 if p_omega is not None else '?'}")
        print(f"  (-ω²/π)₃ directly = ω^{p_neg_omega2}")
        print(f"  (-ω²/π)₃ from parts = ω^{(p_neg1 + 2*p_omega) % 3 if p_neg1 is not None and p_omega is not None else '?'}")
        print(f"  ((1-ω)/π)₃ = ω^{p_1mw}")
        print(f"  ((1-ω)²/π)₃ = ω^{(2*p_1mw)%3 if p_1mw is not None else '?'}")
        print()
        if p_neg_omega2 is not None and p_1mw is not None:
            combined = (p_neg_omega2 + 2*p_1mw) % 3
            print(f"  (3/π)₃ = (-ω²/π)₃ · ((1-ω)/π)₃² = ω^{p_neg_omega2} · ω^{(2*p_1mw)%3} = ω^{combined}")
            print(f"  Direct: (3/π)₃ = ω^{p_3}")
            print(f"  Consistency check: {combined == p_3}")

    # --- Verify: (1-q)² ≡ -3q mod A ---
    lhs = pow(1 - q, 2, A)
    rhs = (-3 * q) % A
    result['(1-q)^2_eq_neg3q'] = (lhs == rhs)
    if verbose:
        print(f"\nVerify (1-q)² ≡ -3q (mod A): {lhs} ≡ {rhs}? {lhs == rhs}")
        # Proof: (1-q)² = 1 - 2q + q² = (q² + q + 1) - 3q = A - 3q ≡ -3q mod A ✓

    # --- User's norm form analysis ---
    if verbose:
        print(f"\nNorm form analysis (assuming 3^q ≡ 1):")
        print(f"  3^q = [(-ω²)(1-ω)²]^q")
        print(f"  = (-ω²)^q · (1-ω)^{{2q}}")
        print(f"  (-ω²)^q = (-1)^q · ω^{{2q}} = -ω^{{2q}}  (q odd)")

        two_q_mod_3 = (2*q) % 3
        print(f"  2q mod 3 = {two_q_mod_3}")
        print(f"  ω^{{2q}} mod π ≡ q^{{2q}} mod A")
        print(f"  q³ ≡ 1 mod A (since A | q³-1): {pow(q, 3, A) == 1}")
        q_2q = pow(q, 2*q, A)
        print(f"  q^{{2q}} mod A = {q_2q}, q mod A = {q%A}")
        print(f"  q^{{2q}} = q^{{2q mod 3}} = q^{two_q_mod_3} mod A")
        if two_q_mod_3 == 1:
            print(f"  So ω^{{2q}} ≡ q mod π, and -ω^{{2q}} ≡ -q mod π")

        print(f"\n  (1-ω)^{{2q}} mod π ≡ (1-q)^{{2q}} mod A")
        one_minus_q_2q = pow(1 - q, 2*q, A)
        print(f"  (1-q)^{{2q}} mod A = {one_minus_q_2q}")
        neg3q_q = pow((-3*q) % A, q, A)
        print(f"  = [(1-q)²]^q = (-3q)^q mod A = {neg3q_q}")
        neg3_q = (pow(-3 % A, q, A) * pow(q, q, A)) % A
        print(f"  = (-3)^q · q^q mod A = {neg3_q}")
        neg1_q = pow(-1 % A, q, A)  # (-1)^q = -1 since q odd
        three_q_val = pow(3, q, A)
        q_q = pow(q, q, A)
        q_mod_3 = q % 3
        print(f"  q^q: q mod 3 = {q_mod_3}, q^q = q^{{q mod 3}} = q^{q_mod_3} mod A")
        print(f"  q^q mod A = {q_q}, q^{q_mod_3} mod A = {pow(q, q_mod_3, A)}")

        if three_q_val == 1:
            print(f"\n  Under 3^q=1: (-3)^q = (-1)^q · 3^q = -1")
            print(f"  So (1-ω)^{{2q}} ≡ -q^q mod π")
            print(f"  And 3^q ≡ (-ω^{{2q}})·(-q^q) = ω^{{2q}} · q^q mod π")
            val = (q_2q * q_q) % A
            print(f"  = q^{{2q}} · q^q = q^{{3q}} = (q³)^q = 1^q = 1 ✓")
            print(f"  Computed: {val}")
            print(f"  CONSISTENT — no contradiction from this level of analysis.")
        else:
            print(f"\n  3^q ≠ 1, so the assumption doesn't hold. No need for contradiction.")

    # --- Explore: ord_A(3) ---
    # Find the order of 3 modulo A
    order = 1
    val = 3
    for i in range(1, A):
        if val % A == 1:
            order = i
            break
        val = (val * 3) % A
    result['ord_A(3)'] = order
    result['q_divides_order'] = (order % q == 0)

    if verbose:
        print(f"\nOrder of 3 mod A:")
        print(f"  ord_A(3) = {order}")
        print(f"  |F_A*| = A-1 = {A-1} = q(q+1) = {q}·{q+1}")
        print(f"  ord | q(q+1)")
        print(f"  q | ord? {order % q == 0}")
        print(f"  (q+1) | ord? {order % (q+1) == 0}")
        print(f"  ord/q = {order // q if order % q == 0 else 'N/A'}")

    # --- Mod π² analysis ---
    if verbose and three_q == 1:
        print(f"\nMod π² analysis:")
        # 3^q ≡ 1 mod A = N(π). What about mod A²?
        three_q_mod_A2 = pow(3, q, A*A)
        print(f"  3^q mod A² = {three_q_mod_A2}")
        print(f"  3^q = 1 + {three_q_mod_A2 - 1} = 1 + {(three_q_mod_A2 - 1)//A}·A + ...")
        if (three_q_mod_A2 - 1) % A == 0:
            print(f"  3^q ≡ 1 (mod A²)! Wieferich-like condition!")
            result['wieferich'] = True
        else:
            c = (three_q_mod_A2 - 1) // A
            print(f"  3^q ≡ 1 + {c}·A (mod A²)")
            print(f"  c mod 3 = {c % 3}")
            result['wieferich'] = False
            result['wieferich_c'] = c

    return result


# ============================================================
# Part 4: Systematic exploration of cubic reciprocity formulas
# ============================================================

def explore_supplement_formula(primes_list):
    """
    For each (q, A), compute ((1-ω)/π)₃ and check against various formulas.
    """
    print(f"\n{'='*70}")
    print("SYSTEMATIC SUPPLEMENT ANALYSIS")
    print(f"{'='*70}")
    print(f"{'q':>8} {'A':>15} {'q%9':>4} {'(1-ω)':>6} {'pred':>5} {'match':>6} {'(ω)':>4} {'(-1)':>5} {'(3)':>4} {'ord':>10}")
    print(f"{'-'*8} {'-'*15} {'-'*4} {'-'*6} {'-'*5} {'-'*6} {'-'*4} {'-'*5} {'-'*4} {'-'*10}")

    for q, A in primes_list:
        exp = (A - 1) // 3
        q_mod = q % A
        q2_mod = pow(q, 2, A)

        def to_p(val):
            if val == 1: return 0
            if val == q_mod: return 1
            if val == q2_mod: return 2
            return None

        p_1mw = to_p(pow((1 - q) % A, exp, A))
        p_omega = to_p(pow(q, exp, A))
        p_neg1 = to_p(pow((-1) % A, exp, A))
        p_3 = to_p(pow(3, exp, A))

        # Find order of 3
        order = 1
        v = 3
        for i in range(1, min(A, 10**7)):
            if v % A == 1:
                order = i
                break
            v = (v * 3) % A
        else:
            order = -1  # too large to compute

        # User's prediction for supplement: ω^{(q+1)/3 mod 3}
        pred = ((q + 1) // 3) % 3
        match = "✓" if pred == p_1mw else "✗"

        print(f"{q:>8} {A:>15} {q%9:>4} {p_1mw:>6} {pred:>5} {match:>6} {p_omega:>4} {p_neg1:>5} {p_3:>4} {order:>10}")


def explore_omega_symbol_formula(primes_list):
    """
    Analyze (ω/π)₃ systematically.

    (ω/π)₃ = ω^{(A-1)/3} in F_A, which means q^{(A-1)/3} mod A.

    (A-1)/3 = q(q+1)/3.
    q^{q(q+1)/3} mod A.
    Since q³ ≡ 1 mod A, exponent reduces mod 3: q(q+1)/3 mod 3.
    q ≡ 2 mod 3: q(q+1)/3 mod 3.
    q+1 ≡ 0 mod 3 (since q ≡ 2 mod 3).
    So q(q+1)/3 = q · ((q+1)/3).
    q ≡ 2 mod 3, (q+1)/3 mod 3 depends on q mod 9.

    For q ≡ 8 mod 9: (q+1)/3 ≡ 3/3 = 1... (q+1) ≡ 0 mod 9, so (q+1)/3 ≡ 0 mod 3.
    Then q · 0 = 0 mod 3. So q^{q(q+1)/3} = q^0 = 1.
    So (ω/π)₃ = 1 for q ≡ 8 mod 9.
    """
    print(f"\n{'='*70}")
    print("ANALYSIS OF (ω/π)₃")
    print(f"{'='*70}")

    for q, A in primes_list[:10]:
        exp = (A - 1) // 3
        q_mod = q % A
        q2_mod = pow(q, 2, A)

        omega_val = pow(q, exp, A)
        if omega_val == 1:
            p = 0
        elif omega_val == q_mod:
            p = 1
        elif omega_val == q2_mod:
            p = 2
        else:
            p = None

        # Theoretical: exp mod 3
        exp_mod_3 = exp % 3  # q^{exp mod 3} since q³ ≡ 1
        q_power = pow(q, exp_mod_3, A)

        print(f"q={q}: (A-1)/3 = {exp}, exp mod 3 = {exp_mod_3}, "
              f"q^(exp mod 3) = {q_power}, (ω/π)₃ = ω^{p}")

        # Alternative: q(q+1)/3 mod 3
        qp1_div3 = (q + 1) // 3
        product_mod3 = (q * qp1_div3) % 3
        print(f"  q(q+1)/3 = {q}·{qp1_div3}, mod 3 = {product_mod3}")


def explore_full_decomposition(primes_list):
    """
    Full decomposition of (3/π)₃ = (-ω²/π)₃ · ((1-ω)/π)₃².

    Check: does this always give (3/π)₃ = 1 for q ≡ 71 mod 72?
    If yes, that's CONSISTENT with 3^q ≡ 1 — no contradiction from this alone.
    If no, that gives a contradiction for specific q!
    """
    print(f"\n{'='*70}")
    print("FULL DECOMPOSITION: (3/π)₃ = (-ω²/π)₃ · ((1-ω)/π)₃²")
    print(f"{'='*70}")
    print(f"{'q':>8} {'3^q≡1?':>7} {'(3/π)':>6} {'(-ω²)':>7} {'(1-ω)':>7} {'combined':>9} {'consist':>8}")

    for q, A in primes_list:
        exp = (A - 1) // 3
        q_mod = q % A
        q2_mod = pow(q, 2, A)

        def to_p(val):
            if val == 1: return 0
            if val == q_mod: return 1
            if val == q2_mod: return 2
            return None

        three_q = pow(3, q, A)
        is_one = (three_q == 1)

        p_3 = to_p(pow(3, exp, A))
        p_neg_w2 = to_p(pow((-pow(q, 2, A)) % A, exp, A))
        p_1mw = to_p(pow((1 - q) % A, exp, A))

        combined = (p_neg_w2 + 2 * p_1mw) % 3 if p_neg_w2 is not None and p_1mw is not None else None
        consist = (combined == p_3) if combined is not None else None

        print(f"{q:>8} {'Y' if is_one else 'N':>7} {p_3:>6} {p_neg_w2:>7} {p_1mw:>7} {combined:>9} {'✓' if consist else '✗':>8}")


def explore_cubic_reciprocity(primes_list):
    """
    Apply cubic reciprocity to compute (3/π)₃ theoretically.

    Actually, since 3 = -ω²(1-ω)², and (1-ω) is the ramified prime,
    we can't directly apply cubic reciprocity to (3/π)₃.

    But we can analyze the structure differently.

    Let λ = 1 - ω (the unique prime above 3 in Z[ω]).
    3 = -ω² λ².

    (3/π)₃ = (-ω²/π)₃ · (λ/π)₃²

    For the (λ/π)₃ part: λ is the ramified prime.
    By the cubic supplement law (Ireland-Rosen Prop 9.3.5):
    For primary π₀ = a + bω (a ≡ 2 mod 3, b ≡ 0 mod 3):
    (λ/π₀)₃ = ω^{(a+b-1+b²(a-1)/3)/3} ...

    Actually the standard result is simpler. Let me look up the exact formula.

    Ireland-Rosen, Chapter 9, Proposition 9.3.5:
    If π is primary (a ≡ 2 mod 3, b ≡ 0 mod 3) and π doesn't divide λ, then:

    (λ/π)₃ = ω^{b/3}   ... No wait, it depends on convention.

    Let me just check computationally.
    """
    print(f"\n{'='*70}")
    print("CUBIC SUPPLEMENT: (λ/π₀)₃ where λ = 1-ω, π₀ primary")
    print(f"{'='*70}")

    for q, A in primes_list[:15]:
        exp = (A - 1) // 3
        q_mod = q % A
        q2_mod = pow(q, 2, A)

        def to_p(val):
            if val == 1: return 0
            if val == q_mod: return 1
            if val == q2_mod: return 2
            return None

        p_lambda = to_p(pow((1 - q) % A, exp, A))

        pi0 = (-OMEGA) * Eisenstein(q, -1)  # -ω(q - ω) = -1 - (q+1)ω
        a, b = pi0.a, pi0.b

        # Various formulas to test:
        # Formula 1: ω^{b/3}
        f1 = (b // 3) % 3
        # Formula 2: ω^{-b/3}
        f2 = (-(b // 3)) % 3
        # Formula 3: ω^{(a-1)/3}
        f3 = ((a - 1) // 3) % 3 if (a - 1) % 3 == 0 else None
        # Formula 4: ω^{(a+b-1)/3}
        f4 = ((a + b - 1) // 3) % 3 if (a + b - 1) % 3 == 0 else None
        # Formula 5: ω^{-(a-1)/3}
        f5 = (-((a - 1) // 3)) % 3 if (a - 1) % 3 == 0 else None

        # For a = -1, b = -(q+1):
        # b/3 = -(q+1)/3
        # (a-1)/3 = -2/3 — not integer! Unless a ≡ 1 mod 3... a = -1 ≡ 2 mod 3, a-1 = -2 ≡ 1 mod 3. Not divisible.
        # Hmm. Let me try the correct formula.
        # Convention: primary means a ≡ 2 mod 3, 3|b.
        # The cubic supplement for (1-ω) as stated in Lemmermeyer:
        # ((1-ω)/π)₃ = ω^{m} where π = a + bω, and m is determined by...

        # Let's just check which formula matches
        matches = []
        if f1 == p_lambda: matches.append("b/3")
        if f2 == p_lambda: matches.append("-b/3")
        if f3 == p_lambda: matches.append("(a-1)/3")
        if f4 == p_lambda: matches.append("(a+b-1)/3")
        if f5 == p_lambda: matches.append("-(a-1)/3")

        # Also try: ω^{(a-1+b)/3}
        f6 = ((a - 1 + b) // 3) % 3 if (a - 1 + b) % 3 == 0 else None
        if f6 == p_lambda: matches.append("(a-1+b)/3")

        # And: ω^{-(a+1)/3}
        f7 = (-(a + 1) // 3) % 3 if (a + 1) % 3 == 0 else None
        if f7 is not None and f7 == p_lambda: matches.append("-(a+1)/3")

        print(f"q={q:>6}: π₀ = {a} + {b}ω, (λ/π₀)₃ = ω^{p_lambda}, "
              f"b/3={b//3}, matches: {matches}")


def deeper_analysis(primes_list):
    """
    Key question: For q ≡ 71 mod 72 with A prime,
    is 3 ALWAYS a cubic residue mod A?

    If (3/π)₃ = 1 always, we can't get a contradiction from the cubic symbol alone.
    We'd need to go deeper (higher power residue symbols, p-adic analysis, etc.)
    """
    print(f"\n{'='*70}")
    print("KEY QUESTION: Is (3/π)₃ = 1 for all q ≡ 71 mod 72?")
    print(f"{'='*70}")

    always_one = True
    for q, A in primes_list:
        exp = (A - 1) // 3
        chi3 = pow(3, exp, A)
        is_cr = (chi3 == 1)
        if not is_cr:
            always_one = False
            print(f"q = {q}: (3/π)₃ ≠ 1! chi3 = {chi3}")

    if always_one:
        print("YES — (3/π)₃ = 1 for all tested q. 3 is always a cubic residue mod A.")
        print("This is EXPECTED: if 3^q ≡ 1 mod A, then 3^{(A-1)/3} = 1.")
        print("But ALSO: even when 3^q ≠ 1, is (3/π)₃ still = 1?")

    # Check: for q where 3^q ≠ 1, what is (3/π)₃?
    print(f"\nq where 3^q ≢ 1 mod A:")
    count_not_one = 0
    for q, A in primes_list:
        three_q = pow(3, q, A)
        if three_q != 1:
            exp = (A - 1) // 3
            chi3 = pow(3, exp, A)
            q_mod = q % A
            q2_mod = pow(q, 2, A)
            if chi3 == 1: p = 0
            elif chi3 == q_mod: p = 1
            elif chi3 == q2_mod: p = 2
            else: p = None
            count_not_one += 1
            if count_not_one <= 20:
                order = 1
                v = 3
                for i in range(1, min(A, 10**7)):
                    if v % A == 1:
                        order = i
                        break
                    v = (v * 3) % A
                print(f"  q={q}: 3^q mod A = {three_q}, (3/π)₃ = ω^{p}, ord(3) = {order}")
    print(f"Total with 3^q ≢ 1: {count_not_one} / {len(primes_list)}")


def explore_higher_power_residue(primes_list):
    """
    Since the cubic residue symbol alone can't distinguish (3 is always a CR
    when 3^q = 1), explore 9th power residue symbols.

    9th power residue: 3^{(A-1)/9} mod A.
    This is defined when 9 | (A-1), i.e., 9 | q(q+1).
    For q ≡ 8 mod 9: q+1 ≡ 0 mod 9, so 9 | (q+1) | q(q+1) = A-1. ✓
    """
    print(f"\n{'='*70}")
    print("9TH POWER RESIDUE ANALYSIS")
    print(f"{'='*70}")

    for q, A in primes_list[:20]:
        if (A - 1) % 9 != 0:
            print(f"q={q}: 9 ∤ (A-1), skip")
            continue

        exp9 = (A - 1) // 9
        chi9 = pow(3, exp9, A)

        # The 9th roots of unity mod A are powers of a primitive 9th root
        # g^{(A-1)/9} where g is a primitive root mod A
        # Find a primitive 9th root of unity
        # ω₉ = g^{(A-1)/9}
        # Or: since ω³ = 1 (3rd root) corresponds to q³ ≡ 1,
        # a 9th root ζ₉ satisfies ζ₉^9 = 1.

        three_q = pow(3, q, A)

        # If 3^q = 1, then 3^{(A-1)/9} = 3^{q(q+1)/9} = (3^q)^{(q+1)/9} = 1^{...} = 1
        # ONLY IF 9 | (q+1). For q ≡ 8 mod 9: q+1 ≡ 0 mod 9. So yes.

        expected_one = (three_q == 1)
        actual_one = (chi9 == 1)

        print(f"q={q}: 3^q≡1? {expected_one}, 3^{{(A-1)/9}} mod A = {chi9}, is 1? {actual_one}")

        if expected_one and not actual_one:
            print(f"  *** IMPOSSIBLE: 3^q=1 should imply 3^(A-1)/9=1 for q≡8 mod 9 ***")
        if not expected_one:
            # More interesting: what is the 9th power residue symbol?
            pass


def explore_order_distribution(primes_list):
    """
    Analyze the distribution of ord_A(3) for q ≡ 71 mod 72.
    Key: if ord_A(3) = q, then 3^q ≡ 1 mod A.
    """
    print(f"\n{'='*70}")
    print("ORDER DISTRIBUTION: ord_A(3) for q ≡ 71 mod 72")
    print(f"{'='*70}")

    order_counts = {}

    for q, A in primes_list:
        # A-1 = q(q+1). Possible orders divide q(q+1).
        # Since q is prime, divisors of q(q+1) = {1, q, d, qd} where d | (q+1).

        # Check: does 3^q ≡ 1 mod A?
        three_q = pow(3, q, A)
        if three_q == 1:
            # ord | q. Since q is prime, ord ∈ {1, q}.
            # 3 ≡ 1 mod A iff A | 2, impossible for A > 2.
            # So ord = q.
            order = q
        else:
            # ord does not divide q. ord | q(q+1) but ord ∤ q.
            # So ord = q+1, or ord divides q+1, or ord = q·d for some d | (q+1), d > 1.
            # Actually: if ord ∤ q, then gcd(ord, q) = 1 (since q is prime and ord ≠ q).
            # So ord | (q+1) (since ord | q(q+1) and gcd(ord, q) = 1).
            # OR: ord = q · d where d | (q+1)? No: if q | ord and ord | q(q+1), then ord = q·d, d | (q+1).
            # But 3^q ≠ 1 means q ∤ ord... wait, no.
            # 3^q ≡ 1 iff ord | q. If 3^q ≠ 1, then ord ∤ q.
            # But ord | q(q+1). Since q is prime, either q | ord or gcd(ord, q) = 1.
            # If gcd(ord, q) = 1, then ord | (q+1).
            # If q | ord, then ord = q·d, d | (q+1). But 3^q ≠ 1 means ord ∤ q,
            # so q | ord but ord > q, i.e., d > 1.

            # Find actual order
            order = None
            # Check divisors of q+1 first
            for d in range(1, q+2):
                if (q+1) % d == 0:
                    if pow(3, d, A) == 1:
                        order = d
                        break

            if order is None:
                # Check q * divisors of (q+1)
                for d in range(1, q+2):
                    if (q+1) % d == 0:
                        if pow(3, q*d, A) == 1:
                            order = q*d
                            break

        if order is not None:
            factor_type = ""
            if order == q:
                factor_type = "q"
            elif order % q == 0:
                d = order // q
                factor_type = f"q·{d}"
            else:
                factor_type = f"{order} | (q+1)"

            key = factor_type if order <= q else ("q·d" if order % q == 0 else "d|(q+1)")
            order_counts[key] = order_counts.get(key, 0) + 1

            if len(primes_list) <= 30 or order == q:
                three_q_str = "1" if three_q == 1 else str(three_q)
                print(f"q={q:>8}: ord_A(3) = {order:>12} = {factor_type:>15}, "
                      f"3^q mod A = {three_q_str}")

    print(f"\nDistribution:")
    for key, count in sorted(order_counts.items()):
        print(f"  {key}: {count} / {len(primes_list)}")


def explore_fermat_quotient(primes_list):
    """
    For cases where 3^q ≡ 1 mod A, analyze the Fermat quotient:
    (3^q - 1) / A mod A.

    This is the "Wieferich" direction — looking at the next term in the expansion.
    """
    print(f"\n{'='*70}")
    print("FERMAT QUOTIENT ANALYSIS: (3^q - 1)/A mod A")
    print(f"{'='*70}")

    for q, A in primes_list:
        three_q = pow(3, q, A)
        if three_q == 1:
            three_q_full = pow(3, q, A*A)
            fq = (three_q_full - 1) // A
            print(f"q={q:>8}: (3^q-1)/A mod A = {fq % A:>12}, "
                  f"(3^q-1)/A mod 3 = {fq % 3}, mod q = {fq % q}")


# ============================================================
# Part 5: Run everything
# ============================================================

if __name__ == '__main__':
    print("FEIT-THOMPSON p=3 CONJECTURE: EISENSTEIN INTEGER ANALYSIS")
    print("=" * 70)
    print("Setup: q prime, q ≡ 71 mod 72 (i.e., q ≡ 2 mod 3, q ≡ 7 mod 8, q ≡ 8 mod 9)")
    print("       A = q² + q + 1 = Φ₃(q), A prime")
    print("Goal: Show 3^q ≢ 1 (mod A)")

    # --- Step 1: Verify 3 = -ω²(1-ω)² ---
    print(f"\n{'='*70}")
    print("VERIFICATION: 3 = -ω²(1-ω)² in Z[ω]")
    print(f"{'='*70}")
    vf = verify_factorization_of_3(0)
    for k, v in vf.items():
        print(f"  {k} = {v}")

    # --- Step 2: Find primes ---
    print(f"\n{'='*70}")
    print("FINDING PRIMES q ≡ 71 mod 72 with A = q²+q+1 prime")
    print(f"{'='*70}")
    primes = find_primes_q_mod_72(40)
    print(f"Found {len(primes)} pairs:")
    for i, (q, A) in enumerate(primes):
        print(f"  {i+1:>3}. q = {q:>10}, A = {A:>20}")

    # --- Step 3: Detailed analysis of first few ---
    for q, A in primes[:3]:
        full_analysis(q, A, verbose=True)

    # --- Step 4: Systematic tables ---
    explore_supplement_formula(primes)
    explore_omega_symbol_formula(primes[:10])
    explore_full_decomposition(primes)
    explore_cubic_reciprocity(primes[:15])
    deeper_analysis(primes)
    explore_higher_power_residue(primes[:15])
    explore_order_distribution(primes)
    explore_fermat_quotient(primes)

    # --- Final summary ---
    print(f"\n{'='*70}")
    print("SUMMARY AND CONCLUSIONS")
    print(f"{'='*70}")

    # Count how many have 3^q ≡ 1
    consistent_count = sum(1 for q, A in primes if pow(3, q, A) == 1)
    print(f"\nOut of {len(primes)} primes q ≡ 71 mod 72 with A prime:")
    print(f"  3^q ≡ 1 mod A: {consistent_count} cases")
    print(f"  3^q ≢ 1 mod A: {len(primes) - consistent_count} cases")

    if consistent_count == 0:
        print("\n*** STRONG EVIDENCE: 3^q ≢ 1 mod A for ALL tested q ≡ 71 mod 72! ***")
        print("The conjecture holds computationally. The cubic residue analysis")
        print("confirms what direct computation shows.")
    elif consistent_count == len(primes):
        print("\n*** SURPRISING: 3^q ≡ 1 mod A for ALL tested cases! ***")
        print("The cubic residue approach gives no contradiction at this level.")
    else:
        print(f"\n*** MIXED: {consistent_count} consistent, {len(primes) - consistent_count} not. ***")
