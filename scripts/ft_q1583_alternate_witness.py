#!/usr/bin/env python3
"""
FT q=1583 Alternate Witness Diagnostic
========================================

slot720/slot736 proved the Feit-Thompson conjecture for (p=3, q) where
q is prime, q > 3, q ≡ 71 (mod 72), q ≤ 1500. The mechanism:

  Given q, find a prime r > 3 dividing A(q) = q^2 + q + 1.
  Then:
    - (q^3 - 1)/(q - 1) = q^2 + q + 1 = A(q)
    - if (q^3-1)/(q-1) | (3^q - 1)/2  then  r | (3^q - 1)/2  then  r | (3^q - 1)
    - i.e. 3^q ≡ 1 (mod r)
    - By Fermat (since r prime, r ∤ 3): 3^(r-1) ≡ 1 (mod r), so 3^q ≡ 3^(q mod (r-1)) (mod r).
    - If 3^(q mod (r-1)) ≢ 1 (mod r), contradiction.

This gives a small-computation witness: we never compute 3^q for large q.

The May 30 debate identified q=1583 as the FIRST PRIMARY OBSTRUCTION when
bumping to q ≤ 2000, because A(1583) = 1583^2 + 1583 + 1 = 2,507,473 is PRIME.
There is no proper small factor of A(1583) to anchor Fermat reduction.

This script:
  1. Verifies A(1583) is prime (no proper factor).
  2. For each candidate small prime r in {2,5,7,11,...,97}, checks:
       - does r divide A(1583)?  (necessary for slot720 mechanism)
       - what is 3^(q mod (r-1)) mod r?
       - would the slot720 reduction give a valid witness?
  3. Reports the full picture and decides:
       (A) alternate witness exists  -> save FT family at q=1583
       (B) no alternate witness      -> family theorem (with this mechanism) BREAKS at 1583

Mathematical note: even when A(1583) is prime, the FT family theorem itself
(¬ A(q) | (3^q-1)/2 for q=1583) MAY STILL BE TRUE — it just cannot be proven by
the slot720 small-witness Fermat reduction. To know whether FT holds at q=1583,
we still need to check whether A(1583) = 2,507,473 itself divides (3^1583 - 1)/2,
which requires computing the order of 3 mod 2,507,473.

Outputs:
  analysis/ft_q1583_diagnostic.json
  analysis/ft_q1583_diagnostic.md
"""

from __future__ import annotations
import json
from pathlib import Path


# -------------------- Number-theory helpers --------------------

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def multiplicative_order(a: int, n: int) -> int | None:
    """Order of a in (Z/nZ)^*, or None if gcd(a,n) != 1."""
    from math import gcd
    if gcd(a, n) != 1:
        return None
    # ord must divide phi(n); here we just iterate up to n
    x = a % n
    k = 1
    while x != 1:
        x = (x * a) % n
        k += 1
        if k > n:
            return None
    return k


# -------------------- slot720 mechanism per candidate r --------------------

def slot720_check(q: int, r: int) -> dict:
    """
    Check whether r is a slot720-style Fermat-reduction witness for q.

    Required for the WITNESS to be valid:
      - r is prime
      - r > 3 (so r ∤ 3)
      - r | A(q) = q^2 + q + 1
      - 3^(q mod (r-1)) mod r != 1

    Returns a dict with the check outcome and intermediate values.
    """
    A = q * q + q + 1
    info: dict = {
        "candidate_r": r,
        "is_prime_r": is_prime(r),
        "r_gt_3": r > 3,
        "A_of_q": A,
        "A_mod_r": A % r,
        "r_divides_A": (A % r == 0),
    }
    if not (info["is_prime_r"] and info["r_gt_3"] and info["r_divides_A"]):
        info["valid_slot720_witness"] = False
        info["reason"] = (
            "fails preconditions (need prime r > 3 with r | A(q))"
        )
        return info

    # Now r is a prime > 3 dividing A(q). Fermat reduce.
    exponent = q % (r - 1)
    val = pow(3, exponent, r)
    info["q_mod_r_minus_1"] = exponent
    info["3_pow_q_reduced_mod_r"] = val
    info["fermat_reduction_gives_one"] = (val == 1)
    info["valid_slot720_witness"] = (val != 1)
    info["reason"] = (
        "valid Fermat-reduction witness" if val != 1
        else "Fermat reduction gives 1, so this r cannot witness FT"
    )
    return info


# -------------------- Direct (no-witness) check at the large prime --------------------

def direct_FT_check(q: int) -> dict:
    """
    Without the small-witness shortcut, compute whether (q^3-1)/(q-1) = A(q)
    divides (3^q - 1)/2 directly.

    This requires:
      - 3^q mod A(q)
      - Is that == 1?  (if so, A(q) | (3^q - 1))  and  A(q) odd  so  A(q) | (3^q-1)/2
        which WOULD make FT_p3_q false at this q.

    For q=1583 this is feasible with built-in modpow even though A(q) ~ 2.5M.
    """
    A = q * q + q + 1
    val = pow(3, q, A)  # 3^q mod A(q)
    return {
        "q": q,
        "A_of_q": A,
        "A_is_prime": is_prime(A),
        "3_pow_q_mod_A": val,
        "3_pow_q_equiv_1_mod_A": (val == 1),
        # FT_p3_q at this q says: NOT( A(q) | (3^q-1)/2 ).
        # Since A(q) is odd, A(q) | (3^q-1)/2 iff A(q) | (3^q-1) iff 3^q ≡ 1 mod A(q).
        # So FT_p3_q holds iff 3^q mod A(q) != 1.
        "FT_p3_q_holds_at_this_q": (val != 1),
        # Order of 3 mod A(q)
        "ord_3_mod_A": multiplicative_order(3, A),
    }


# -------------------- Main diagnostic --------------------

def run_diagnostic() -> dict:
    q = 1583
    candidates = [2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                  53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

    A = q * q + q + 1
    A_factors = factor(A)

    # Per-candidate slot720-style check
    per_candidate = [slot720_check(q, r) for r in candidates]

    # Even smaller-witness sanity: search ALL primes < 200 dividing A(q)
    full_small_scan = []
    for r in range(2, 200):
        if is_prime(r):
            res = slot720_check(q, r)
            if res["r_divides_A"]:
                full_small_scan.append(res)

    direct = direct_FT_check(q)

    alt_witness_found = any(c["valid_slot720_witness"] for c in per_candidate)
    any_small_divisor_of_A = any(c["r_divides_A"] for c in per_candidate)

    # Also: comparison vs the family members slot720 already covered.
    # For each q in slot720 (q ≤ 1000), record (q, A(q), small_factor_used, valid_witness).
    slot720_known = [
        (71, 5113, None),     # uses native_decide for q ≤ 100
        (359, 129241, 7),
        (431, 186193, 7),
        (503, 253513, 13),
        (647, 419257, 211),
        (719, 517681, 487),
        (863, 745633, 7),
    ]
    family_members_summary = []
    for (qq, Aq, r_used) in slot720_known:
        family_members_summary.append({
            "q": qq,
            "A_q": Aq,
            "A_q_check": qq * qq + qq + 1,
            "A_q_factors": factor(Aq),
            "A_q_is_prime": is_prime(Aq),
            "small_prime_factor_used": r_used,
        })

    # Find q ≡ 71 mod 72, q prime, q ≤ 2000, and check A(q) prime?
    structural_scan = []
    for qq in range(5, 2001):
        if qq % 72 == 71 and is_prime(qq):
            Aq = qq * qq + qq + 1
            fac = factor(Aq)
            structural_scan.append({
                "q": qq,
                "A_q": Aq,
                "A_q_is_prime": is_prime(Aq),
                "smallest_prime_factor": min(fac.keys()),
                "n_distinct_prime_factors": len(fac),
            })

    # Of those structural scans, which q in [1500, 2000] would slot720 mechanism BREAK on?
    breakpoints_2000 = [
        s for s in structural_scan
        if s["q"] > 1500 and (s["A_q_is_prime"] or s["smallest_prime_factor"] > 1000)
    ]

    diagnostic = {
        "q": q,
        "q_is_prime": is_prime(q),
        "q_mod_72": q % 72,
        "in_family": (is_prime(q) and q > 3 and q % 72 == 71),
        "A_of_q": A,
        "A_factorization": A_factors,
        "A_is_prime": is_prime(A),
        "slot720_mechanism": (
            "Find prime r > 3 with r | A(q). Fermat-reduce 3^q mod r as "
            "3^(q mod (r-1)) mod r. If != 1, FT holds at this q (witness r)."
        ),
        "per_small_candidate_checks": per_candidate,
        "all_small_primes_lt_200_dividing_A": full_small_scan,
        "alternate_witness_found": alt_witness_found,
        "any_small_divisor_of_A_in_candidate_set": any_small_divisor_of_A,
        "direct_FT_check_at_A": direct,
        "slot720_known_family_members": family_members_summary,
        "structural_scan_q_equiv_71_mod_72_le_2000": structural_scan,
        "predicted_breakpoints_in_1500_2000": breakpoints_2000,
        "conclusion": _make_conclusion(alt_witness_found, direct, A),
    }
    return diagnostic


def _make_conclusion(alt_witness_found: bool, direct: dict, A: int) -> dict:
    if alt_witness_found:
        return {
            "branch": "alternate_witness",
            "headline": (
                "An alternate small-prime Fermat-reduction witness exists for q=1583. "
                "The slot720 family theorem can be saved at q=1583 via this witness."
            ),
            "witness_r": None,  # filled out below if reachable
        }
    # No small witness available.
    ft_holds = direct["FT_p3_q_holds_at_this_q"]
    if ft_holds:
        # A(q) is prime and 3^q != 1 mod A(q), so FT_p3_q holds at q=1583 but ONLY via
        # direct computation mod A(q) ~ 2.5M, NOT via the slot720 mechanism.
        return {
            "branch": "no_small_witness_but_FT_holds_by_direct_mod_A",
            "headline": (
                "No small (r ≤ 97 or even r < 200) Fermat-reduction witness exists "
                "because A(1583) = 2,507,473 is itself prime. The slot720 small-witness "
                "MECHANISM breaks at q=1583. FT_p3_q still holds at q=1583 by direct "
                "computation: 3^1583 mod A(1583) != 1. So the family theorem is TRUE at "
                "q=1583 but requires a different (large-prime, direct-modpow) proof tactic."
            ),
            "FT_p3_q_at_1583_true": True,
            "mechanism_breaks": True,
        }
    else:
        return {
            "branch": "falsification",
            "headline": (
                "No small witness AND 3^1583 ≡ 1 mod A(1583). FT_p3_q FAILS at q=1583. "
                "This would be a counterexample to the family theorem."
            ),
            "FT_p3_q_at_1583_true": False,
            "mechanism_breaks": True,
        }


# -------------------- I/O --------------------

REPO = Path(__file__).resolve().parents[1]
OUT_JSON = REPO / "analysis" / "ft_q1583_diagnostic.json"
OUT_MD = REPO / "analysis" / "ft_q1583_diagnostic.md"


def write_outputs(diag: dict) -> None:
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(diag, indent=2, default=str))

    lines: list[str] = []
    lines.append("# FT q=1583 Alternate-Witness Diagnostic")
    lines.append("")
    lines.append("Generated by `scripts/ft_q1583_alternate_witness.py` to investigate")
    lines.append("whether the slot720/slot736 Feit-Thompson family mechanism can be")
    lines.append("salvaged at q=1583, where A(q) = q^2 + q + 1 is prime.")
    lines.append("")
    lines.append("## Setup")
    lines.append("")
    lines.append(f"- q = {diag['q']}")
    lines.append(f"- q prime? {diag['q_is_prime']}")
    lines.append(f"- q mod 72 = {diag['q_mod_72']}  (in family ≡ 71 mod 72: {diag['in_family']})")
    lines.append(f"- A(q) = q^2 + q + 1 = {diag['A_of_q']:,}")
    lines.append(f"- A(q) factorization: {diag['A_factorization']}")
    lines.append(f"- A(q) is prime? **{diag['A_is_prime']}**")
    lines.append("")
    lines.append("## slot720 mechanism (exact)")
    lines.append("")
    lines.append("slot720's `feit_thompson_p3_q71_family` claim for a single q in the")
    lines.append("family is:")
    lines.append("")
    lines.append("```")
    lines.append("¬ (q^3 - 1) / (q - 1) ∣ (3^q - 1) / 2")
    lines.append("```")
    lines.append("")
    lines.append("Note that `(q^3 - 1)/(q - 1) = q^2 + q + 1 = A(q)`. The proof tactic")
    lines.append("uses the helper `not_dvd_via_fermat_factor q r ...` requiring")
    lines.append("**a small prime r > 3 with r | A(q)** and `3^(q mod (r-1)) ≢ 1 (mod r)`.")
    lines.append("")
    lines.append("For q=1583 the claim is:")
    lines.append("")
    lines.append(f"  `¬ {diag['A_of_q']} ∣ (3^1583 - 1) / 2`")
    lines.append("")
    lines.append("equivalently `3^1583 ≢ 1 (mod 2,507,473)`.")
    lines.append("")
    lines.append("## Per-candidate small-prime witness scan")
    lines.append("")
    lines.append("Candidates tested: r ∈ {2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,")
    lines.append("43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}.")
    lines.append("")
    lines.append("| r | prime | r>3 | r \\| A(1583) | A mod r | valid slot720 witness? | reason |")
    lines.append("|---|-------|-----|--------------|---------|------------------------|--------|")
    for c in diag["per_small_candidate_checks"]:
        lines.append(
            f"| {c['candidate_r']} | {c['is_prime_r']} | {c['r_gt_3']} | "
            f"{c['r_divides_A']} | {c['A_mod_r']} | {c['valid_slot720_witness']} | {c['reason']} |"
        )
    lines.append("")
    lines.append("Extended scan (all primes r < 200 dividing A(1583)):")
    lines.append("")
    if diag["all_small_primes_lt_200_dividing_A"]:
        for c in diag["all_small_primes_lt_200_dividing_A"]:
            lines.append(f"- r={c['candidate_r']}: valid_witness={c['valid_slot720_witness']}")
    else:
        lines.append("- **NONE**. No prime r < 200 divides A(1583) = 2,507,473.")
    lines.append("")
    lines.append("## Direct check at A(q) itself")
    lines.append("")
    d = diag["direct_FT_check_at_A"]
    lines.append(f"- 3^1583 mod {d['A_of_q']} = {d['3_pow_q_mod_A']}")
    lines.append(f"- 3^1583 ≡ 1 (mod A(1583))? **{d['3_pow_q_equiv_1_mod_A']}**")
    lines.append(f"- ord_3 mod A(1583) = {d['ord_3_mod_A']}")
    lines.append(f"- FT_p3_q at q=1583 holds (i.e. A(q) ∤ (3^q-1)/2)? **{d['FT_p3_q_holds_at_this_q']}**")
    lines.append("")
    lines.append("## Known slot720 family members (sanity)")
    lines.append("")
    lines.append("| q | A(q) | A(q) factors | A(q) prime? | small witness used |")
    lines.append("|---|------|--------------|-------------|--------------------|")
    for m in diag["slot720_known_family_members"]:
        lines.append(
            f"| {m['q']} | {m['A_q']:,} | {m['A_q_factors']} | "
            f"{m['A_q_is_prime']} | {m['small_prime_factor_used']} |"
        )
    lines.append("")
    lines.append("## Structural scan: family q ≡ 71 (mod 72) up to 2000")
    lines.append("")
    lines.append("| q | A(q) | A(q) prime? | smallest prime factor | #distinct prime factors |")
    lines.append("|---|------|-------------|------------------------|--------------------------|")
    for s in diag["structural_scan_q_equiv_71_mod_72_le_2000"]:
        lines.append(
            f"| {s['q']} | {s['A_q']:,} | {s['A_q_is_prime']} | "
            f"{s['smallest_prime_factor']:,} | {s['n_distinct_prime_factors']} |"
        )
    lines.append("")
    lines.append("## Predicted breakpoints in (1500, 2000]")
    lines.append("")
    if diag["predicted_breakpoints_in_1500_2000"]:
        for b in diag["predicted_breakpoints_in_1500_2000"]:
            lines.append(
                f"- q={b['q']}: A(q)={b['A_q']:,}, "
                f"A_is_prime={b['A_q_is_prime']}, smallest_factor={b['smallest_prime_factor']:,}"
            )
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Conclusion")
    lines.append("")
    c = diag["conclusion"]
    lines.append(f"**Branch: `{c['branch']}`**")
    lines.append("")
    lines.append(c["headline"])
    OUT_MD.write_text("\n".join(lines))


if __name__ == "__main__":
    diag = run_diagnostic()
    write_outputs(diag)
    print("Wrote:")
    print(f"  {OUT_JSON}")
    print(f"  {OUT_MD}")
    print()
    print("Branch:", diag["conclusion"]["branch"])
    print("Headline:", diag["conclusion"]["headline"])
