#!/usr/bin/env python3
"""
Numerical experiments for Erdos Problem 267:

    If n_1 < n_2 < ... with n_{k+1} / n_k >= c > 1, must
        sum_k 1 / F_{n_k}
    be irrational?

This script does not prove irrationality. It does three useful things:

1. Builds exact rational partial sums s_t = sum_{k<=t} 1/F_{n_k}.
2. Adds a rigorous tail bound using F_m >= phi^(m-2), hence
       sum_{m>N} 1/F_m <= phi^(3-N),
   so the omitted subsequence tail after index N is at most phi^(3-N).
3. Reports the quantity q_t * tail_t, where q_t is the reduced
   denominator of s_t. If this tends to 0 along infinitely many t,
   rationality is impossible.

Heuristic lesson:
  - For very sparse sequences (roughly ratio > 2), the partial sums
    themselves can already be "too good" to converge to a rational.
  - For ratio near 2 or below, this crude method becomes borderline or fails.
    That is exactly where deeper structure (continued fractions, Mahler-style
    identities, gap-series arguments) would need to enter.
"""

from __future__ import annotations

import argparse
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from typing import Callable


def fibonacci_table(n_max: int) -> list[int]:
    """Return [0, F_1, ..., F_n_max] with exact integers."""
    if n_max < 1:
        return [0, 1]
    fibs = [0, 1, 1]
    for _ in range(3, n_max + 1):
        fibs.append(fibs[-1] + fibs[-2])
    return fibs


def decimal_constants(precision: int) -> tuple[Decimal, Decimal, Decimal]:
    with localcontext() as ctx:
        ctx.prec = precision
        sqrt5 = Decimal(5).sqrt()
        phi = (Decimal(1) + sqrt5) / Decimal(2)
        log10_phi = phi.ln() / Decimal(10).ln()
        return sqrt5, phi, log10_phi


def fraction_to_decimal(value: Fraction, precision: int) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = precision
        return Decimal(value.numerator) / Decimal(value.denominator)


def scientific_notation(x: Decimal, digits: int = 6) -> str:
    if x.is_zero():
        return "0"
    with localcontext() as ctx:
        ctx.prec = max(digits + 8, 20)
        return format(x, f".{digits}E")


def log10_int(n: int) -> float:
    """Stable log10 for huge integers without decimal string conversion."""
    if n <= 0:
        raise ValueError("expected positive integer")
    bits = n.bit_length()
    shift = max(bits - 60, 0)
    top = n >> shift
    return math.log10(top) + shift * math.log10(2)


def continued_fraction(x: Decimal, terms: int, precision: int) -> list[int]:
    coeffs: list[int] = []
    with localcontext() as ctx:
        ctx.prec = precision
        y = +x
        for _ in range(terms):
            a = int(y)
            coeffs.append(a)
            frac = y - a
            if not frac:
                break
            y = Decimal(1) / frac
    return coeffs


def convergents(coeffs: list[int]) -> list[Fraction]:
    out: list[Fraction] = []
    p_nm2, p_nm1 = 0, 1
    q_nm2, q_nm1 = 1, 0
    for a in coeffs:
        p_n = a * p_nm1 + p_nm2
        q_n = a * q_nm1 + q_nm2
        out.append(Fraction(p_n, q_n))
        p_nm2, p_nm1 = p_nm1, p_n
        q_nm2, q_nm1 = q_nm1, q_n
    return out


def powers(base: int, terms: int, start_exp: int = 1) -> list[int]:
    return [base**k for k in range(start_exp, start_exp + terms)]


def ceiling_ratio_sequence(ratio: float, terms: int, start: int = 2) -> list[int]:
    out = [start]
    while len(out) < terms:
        nxt = math.ceil(ratio * out[-1])
        if nxt <= out[-1]:
            nxt = out[-1] + 1
        out.append(nxt)
    return out


def floor_power_sequence(alpha: float, terms: int, start_exp: int = 2) -> list[int]:
    out: list[int] = []
    last = 0
    k = start_exp
    while len(out) < terms:
        nxt = math.floor(alpha**k)
        if nxt > last:
            out.append(nxt)
            last = nxt
        k += 1
    return out


def double_plus_one_sequence(terms: int, start: int = 1) -> list[int]:
    out = [start]
    while len(out) < terms:
        out.append(2 * out[-1] + 1)
    return out


SEQUENCES: dict[str, Callable[[int], list[int]]] = {
    "pow2": lambda terms: powers(2, terms),
    "pow3": lambda terms: powers(3, terms),
    "ceil_1p6": lambda terms: ceiling_ratio_sequence(1.6, terms),
    "ceil_1p95": lambda terms: ceiling_ratio_sequence(1.95, terms),
    "double_plus_one": double_plus_one_sequence,
    "floor_pi": lambda terms: floor_power_sequence(math.pi, terms),
}


def validate_sequence(indices: list[int]) -> None:
    if not indices:
        raise ValueError("empty sequence")
    if any(n < 1 for n in indices):
        raise ValueError("indices must be >= 1")
    if any(b <= a for a, b in zip(indices, indices[1:])):
        raise ValueError("sequence must be strictly increasing")


def format_ratio_stats(indices: list[int]) -> str:
    if len(indices) < 2:
        return "n/a"
    ratios = [b / a for a, b in zip(indices, indices[1:])]
    return f"min={min(ratios):.4f} max={max(ratios):.4f}"


def checkpoint_terms(total_terms: int) -> list[int]:
    raw = [4, 6, 8, 10, 12, total_terms]
    return sorted({t for t in raw if 1 <= t <= total_terms})


def tail_bound(last_index: int, phi: Decimal, precision: int) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = precision
        return phi ** (3 - last_index)


def analyze_sequence(
    name: str,
    indices_with_next: list[int],
    fibs: list[int],
    digits: int,
    cf_terms: int,
) -> None:
    validate_sequence(indices_with_next)
    indices = indices_with_next[:-1]
    next_indices = indices_with_next[1:]
    precision = digits + 40
    _, phi, log10_phi = decimal_constants(precision)
    checkpoints = checkpoint_terms(len(indices))

    print(f"== {name} ==")
    print(f"indices[:12] = {indices[:12]}")
    print(f"ratio stats  = {format_ratio_stats(indices)}")
    print("t   n_t   next n   log10(q_t)   tail_bound         log10(q_t * tail)")

    partial = Fraction(0, 1)
    for t, n_t in enumerate(indices, start=1):
        partial += Fraction(1, fibs[n_t])
        if t not in checkpoints:
            continue
        next_n = next_indices[t - 1]
        log10_q = log10_int(partial.denominator)
        tail = tail_bound(next_n, phi, precision)
        log10_q_tail = Decimal(log10_q) + (Decimal(3 - next_n) * log10_phi)
        print(
            f"{t:2d}  {n_t:4d}  {next_n:6d}  {log10_q:10.3f}   "
            f"{scientific_notation(tail):>14}   {log10_q_tail:>16.6f}"
        )

    approx = fraction_to_decimal(partial, precision)
    cf = continued_fraction(approx, cf_terms, precision)
    convs = convergents(cf)
    final_tail = tail_bound(indices_with_next[-1], phi, precision)

    print(f"partial sum ≈ {approx}")
    print(
        f"rigorous tail after n_t={indices[-1]} "
        f"(using next index {indices_with_next[-1]}): <= {scientific_notation(final_tail, 10)}"
    )
    print(f"continued fraction (heuristic, first {len(cf)} terms): {cf}")
    print("first convergents:")
    for i, frac in enumerate(convs[: min(6, len(convs))], start=1):
        err = abs(approx - fraction_to_decimal(frac, precision))
        print(
            f"  c{i}: {frac.numerator}/{frac.denominator}  "
            f"err≈{scientific_notation(err)}"
        )
    print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--terms",
        type=int,
        default=8,
        help="number of terms from each lacunary sequence",
    )
    parser.add_argument(
        "--digits",
        type=int,
        default=80,
        help="decimal digits for the displayed approximation",
    )
    parser.add_argument(
        "--cf-terms",
        type=int,
        default=14,
        help="continued-fraction terms to display",
    )
    parser.add_argument(
        "--sequence",
        action="append",
        choices=sorted(SEQUENCES),
        help="sequence(s) to analyze; default is a representative bundle",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    names = args.sequence or [
        "pow2",
        "pow3",
        "ceil_1p6",
        "ceil_1p95",
        "double_plus_one",
    ]
    all_indices = {name: SEQUENCES[name](args.terms + 1) for name in names}
    max_index = max(max(indices) for indices in all_indices.values())
    fibs = fibonacci_table(max_index)

    print("Erdos 267 numerical experiment")
    print(f"terms={args.terms} digits={args.digits} cf_terms={args.cf_terms}")
    print()
    for name in names:
        analyze_sequence(name, all_indices[name], fibs, args.digits, args.cf_terms)


if __name__ == "__main__":
    main()
