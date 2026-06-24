#!/usr/bin/env python3
"""
Erdos Problem 406: search for powers of 2 whose base-3 expansion uses
only the digits 0 and 1.

WHY this implementation is small and fast:
We keep the ternary digits of 2^n directly and update them by repeated
doubling in base 3. That avoids rebuilding huge integers or converting
back and forth between bases on every step.
"""

from __future__ import annotations

import argparse
import time
from dataclasses import dataclass


@dataclass(frozen=True)
class Hit:
    exponent: int
    ternary_length: int
    ones_count: int
    ternary: str


def double_base3_digits(digits: list[int], count_twos: int) -> int:
    """Replace the base-3 digit vector by twice its value and return the new number of 2 digits."""
    carry = 0
    for i, digit in enumerate(digits):
        if digit == 2:
            count_twos -= 1
        value = 2 * digit + carry
        new_digit = value % 3
        digits[i] = new_digit
        if new_digit == 2:
            count_twos += 1
        carry = value // 3
    while carry:
        new_digit = carry % 3
        digits.append(new_digit)
        if new_digit == 2:
            count_twos += 1
        carry //= 3
    return count_twos


def digits_use_only_zero_one(count_twos: int) -> bool:
    return count_twos == 0


def digits_to_string(digits: list[int]) -> str:
    return "".join(str(d) for d in reversed(digits))


def search_hits(max_n: int, progress_every: int) -> list[Hit]:
    if max_n < 0:
        raise ValueError("max_n must be >= 0")

    hits: list[Hit] = []
    digits = [1]  # ternary digits of 2^0
    count_twos = 0
    started = time.time()

    if digits_use_only_zero_one(count_twos):
        hits.append(
            Hit(
                exponent=0,
                ternary_length=1,
                ones_count=1,
                ternary="1",
            )
        )

    for n in range(1, max_n + 1):
        count_twos = double_base3_digits(digits, count_twos)

        if digits_use_only_zero_one(count_twos):
            ternary = digits_to_string(digits)
            hits.append(
                Hit(
                    exponent=n,
                    ternary_length=len(digits),
                    ones_count=sum(digits),
                    ternary=ternary,
                )
            )

        if progress_every and n % progress_every == 0:
            elapsed = time.time() - started
            rate = n / max(elapsed, 1e-9)
            print(
                f"[n={n:,}/{max_n:,}] ternary_len={len(digits):,} "
                f"hits={len(hits)} rate={rate:,.0f} exponents/s",
                flush=True,
            )

    return hits


def print_hits(hits: list[Hit], max_show_digits: int) -> None:
    if not hits:
        print("No hits found.")
        return

    print(f"Found {len(hits)} hits:")
    for hit in hits:
        ternary = hit.ternary
        if max_show_digits > 0 and len(ternary) > max_show_digits:
            keep = max_show_digits // 2
            ternary = f"{ternary[:keep]}...{ternary[-keep:]}"
        print(
            f"n={hit.exponent:5d}  len_3={hit.ternary_length:5d}  "
            f"ones={hit.ones_count:4d}  2^n(base 3)={ternary}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--max-n",
        type=int,
        default=10_000,
        help="search exponents n in 0..max_n",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=1_000,
        help="print progress every this many exponents (0 disables)",
    )
    parser.add_argument(
        "--max-show-digits",
        type=int,
        default=120,
        help="truncate printed ternary expansions longer than this many digits",
    )
    args = parser.parse_args()

    hits = search_hits(max_n=args.max_n, progress_every=args.progress_every)
    print_hits(hits, max_show_digits=args.max_show_digits)


if __name__ == "__main__":
    main()
