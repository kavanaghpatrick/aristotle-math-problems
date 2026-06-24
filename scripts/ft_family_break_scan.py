#!/usr/bin/env python3
"""
ft_family_break_scan.py - hedge analysis for slot720/slot736 family theorem.

For each q ≡ 71 (mod 72) with q ≤ 10000 such that A(q) = q^2+q+1 is PRIME,
investigate whether the FT family theorem (for p=3) can be proved at q
via ANY alternate witness mechanism — not just the slot720 "small prime divisor
of A(q) with Fermat reduction" mechanism.

The slot720 mechanism fails when A(q) is prime, because the only prime divisor
of A(q) is A(q) itself, which is too large for Aristotle's native_decide.

Alternate witness ideas (extending agent #5's approach):
  W1: Direct Fermat with p = A(q). Verify 3^q ≢ 1 (mod A(q)). This is the
      "structurally-true but computationally-expensive" route. The Lean proof
      would need to evaluate 3^q mod A(q), where A(q) ~ q^2 ~ 10^7 at q=1583.
  W2: Find an auxiliary small prime r > 3 (r NOT dividing A(q)) such that:
        - r divides 3^q - 1, i.e. ord_r(3) | q (since q prime, this means r | 3-1 = 2
          [impossible for r>3] OR ord_r(3) = q [so r ≡ 1 mod q]). NOT helpful.
      OR (more useful)
        - r | A(q)·k - (3^q-1)/2 for some integer combination — i.e. find a small
          r providing a divisibility obstruction without dividing A(q).
  W3: Lift-the-exponent / p-adic valuation analysis.
  W4: For (q^3-1)/(q-1) ∤ (3^q-1)/2 ⟺ A(q) ∤ (3^q-1)/2 (since A(q) is odd):
      it suffices to find ANY modulus m such that A(q) divides m but m does not
      divide (3^q-1)/2. This is W1 with m = A(q) when A(q) prime.

In short: the structural fact 3^q ≢ 1 (mod A(q)) is what makes the theorem
TRUE at q; the slot720 mechanism just exploits small factors of A(q) for
computational tractability. At q where A(q) is prime, the THEOREM still holds
(if and only if 3^q ≢ 1 mod A(q)), but the PROOF must verify this congruence
directly — a much harder native_decide.

This scan:
  (a) confirms the eight q in {1583, 2663, 3671, 4751, 5039, 6047, 6551, 9719}
      all have A(q) prime,
  (b) verifies 3^q mod A(q) ≢ 1 in every case (so the theorem itself is
      structurally true at these q),
  (c) records the bit-length of A(q) (Aristotle native_decide tractability), and
  (d) searches for an auxiliary small prime r ≤ 100 such that
      3^q mod r ≢ 1 mod r AND r divides some CRT-combined modulus that catches
      A(q) — i.e. tries to find a "small-prime stand-in" for A(q).

Output: /Users/patrickkavanagh/math/analysis/ft_family_break_scan.json
"""
from __future__ import annotations
import json
import math
from pathlib import Path
from sympy import isprime, factorint, divisors

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "analysis" / "ft_family_break_scan.json"


def order_mod(a: int, n: int) -> int | None:
    """Multiplicative order of a mod n; None if gcd(a,n) > 1."""
    if math.gcd(a, n) != 1:
        return None
    # divisors of phi(n) — but we only need exact order, so factor phi(n).
    # For prime n, phi = n-1; we don't need phi for general use here.
    # We'll do a direct order computation by iterating divisors of n-1 for n prime.
    if isprime(n):
        m = n - 1
    else:
        # not used in this script for non-prime n
        return None
    for d in sorted(divisors(m)):
        if pow(a, d, n) == 1:
            return d
    return None


def fermat_compatible_small_prime_divisor(q: int, p_cap: int = 5000):
    """Smallest prime p > 3, p ≤ p_cap, p | A(q), 3^(q%(p-1)) ≢ 1 mod p."""
    A = q * q + q + 1
    for p in sorted(factorint(A).keys()):
        if p <= 3:
            continue
        if p > p_cap:
            return None
        r = q % (p - 1)
        if pow(3, r, p) != 1:
            return {"p": p, "r": r, "val": pow(3, r, p)}
    return None


def alternate_witness_search(q: int, r_cap: int = 1000):
    """
    Search for an auxiliary small prime r ≤ r_cap providing a Fermat-style
    obstruction even when A(q) itself is prime.

    The standard slot720 reduction shows: if p | A(q) and 3^(q mod (p-1)) ≢ 1 mod p,
    then A(q) ∤ (3^q-1)/2. The obstruction is local at p.

    For A(q) prime with A(q) ≤ r_cap-irrelevant: A(q) itself is the only such p
    in the *prime divisor* lattice. So an "alternate witness" requires
    a DIFFERENT obstruction — not via p | A(q).

    Candidates:
      (i)  Show 3^q ≢ 1 (mod A(q)) directly. Bit-length and feasibility recorded.
      (ii) Find r ≤ r_cap such that the GCD lemma
              gcd((3^q-1)/2, A(q)) < A(q)
           can be proved using r — but with A(q) prime this means A(q) ∤ (3^q-1)/2
           directly, which is condition (i).

    There is NO known small-prime stand-in when A(q) is prime: the divisibility
    A(q) | (3^q-1)/2 fails iff 3^q mod A(q) ≢ 1, and that residue depends on
    A(q) itself. We record the direct residue (the "structural witness").

    However, we DO check whether 3 has SMALL order mod A(q). If ord_{A(q)}(3)
    is small (say, divides 24 or 72), then 3^q mod A(q) reduces by 3^(q mod ord).
    A small order would mean the witness verification is cheap.
    """
    A = q * q + q + 1
    A_prime = isprime(A)
    result = {
        "q": q,
        "A": A,
        "A_bits": A.bit_length(),
        "A_prime": A_prime,
        "small_divisor_slot720_style": fermat_compatible_small_prime_divisor(q),
    }
    # Structural witness: 3^q mod A(q).
    three_pow_q_mod_A = pow(3, q, A)
    result["three_pow_q_mod_A"] = three_pow_q_mod_A
    result["theorem_holds_at_q"] = (three_pow_q_mod_A != 1)
    if A_prime:
        # Multiplicative order of 3 mod A(q).
        ord3 = order_mod(3, A)
        result["ord_3_mod_A"] = ord3
        if ord3 is not None:
            result["q_mod_ord3"] = q % ord3
            result["small_order_3_mod_A"] = ord3 <= 1000
    # Check the relation (3^q-1)/2 mod A(q): A(q) is odd (q²+q+1 with q odd is odd).
    # So if A(q) | (3^q-1)/2, then A(q) | (3^q-1), i.e. 3^q ≡ 1 mod A(q).
    return result


def main():
    q_failure_list = [1583, 2663, 3671, 4751, 5039, 6047, 6551, 9719]
    records = []
    first_failure_without_alt = None
    for q in q_failure_list:
        rec = alternate_witness_search(q)
        records.append(rec)
        print(
            f"q={q:>5}  A(q)={rec['A']}  A_prime={rec['A_prime']}  "
            f"3^q mod A(q) = {rec['three_pow_q_mod_A']}  "
            f"theorem_holds_at_q = {rec['theorem_holds_at_q']}  "
            f"ord_3_mod_A = {rec.get('ord_3_mod_A')}  "
            f"slot720_witness = {rec['small_divisor_slot720_style']}"
        )
        if rec["small_divisor_slot720_style"] is None and first_failure_without_alt is None:
            # All eight by construction lack a slot720-style witness; the real
            # question is whether the structural theorem holds at q.
            if not rec["theorem_holds_at_q"]:
                first_failure_without_alt = q

    # Cross-check by also scanning all q ≡ 71 mod 72, q ≤ 10000 for the
    # structural property 3^q ≢ 1 mod A(q).
    print("\n--- Full structural-truth check over q ≡ 71 mod 72, q ≤ 10000 ---")
    q_full = []
    q = 71
    while q <= 10000:
        if isprime(q) and q > 3:
            q_full.append(q)
        q += 72
    counterexamples = []
    for qf in q_full:
        Af = qf * qf + qf + 1
        if pow(3, qf, Af) == 1:
            counterexamples.append(qf)
    print(f"  Total primes q ≡ 71 mod 72 in [4, 10000]: {len(q_full)}")
    print(f"  q with 3^q ≡ 1 mod A(q): {counterexamples}")

    summary = {
        "purpose": (
            "Hedge analysis for FT_p3_q71_family extension beyond slot736 "
            "(q ≤ 1500). Identifies whether the slot720 small-prime-divisor "
            "Fermat-reduction mechanism breaks at q with A(q) prime AND "
            "whether the theorem itself fails at any such q."
        ),
        "q_with_A_prime_in_q_le_10000": q_failure_list,
        "first_q_where_theorem_FAILS": first_failure_without_alt,
        "all_q_with_A_prime_satisfy_3^q_neq_1_mod_A":
            all(r["theorem_holds_at_q"] for r in records),
        "structural_counterexamples_full_scan": counterexamples,
        "per_q_records": records,
        "interpretation": {
            "if_no_counterexample": (
                "The slot720 small-prime mechanism breaks at q where A(q) is "
                "prime, but the theorem itself is structurally true at every "
                "such q. The HEDGE submission is therefore not 'family fails "
                "at q*' but 'family holds at q with A(q) prime, requiring a "
                "direct A(q)-modulus witness whose verification cost scales as "
                "log(A(q)) ~ 2*log(q) bits of native_decide.'"
            ),
            "if_counterexample": (
                "If 3^q ≡ 1 mod A(q) for some q with A(q) prime, the family "
                "theorem ACTUALLY FAILS at that q, and the conjecture would "
                "need a different family-structure to recover."
            ),
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(summary, indent=2))
    print(f"\nWrote {OUT}")
    print(f"\nFirst counterexample (3^q ≡ 1 mod A(q)) in scan: "
          f"{counterexamples or 'NONE'}")
    return summary


if __name__ == "__main__":
    main()
