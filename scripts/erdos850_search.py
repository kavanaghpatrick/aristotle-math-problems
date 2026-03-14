"""
Erdos Problem 850 (k=3) computational search.

We seek distinct positive integers x,y such that:
  rad(x)   = rad(y)
  rad(x+1) = rad(y+1)
  rad(x+2) = rad(y+2)

Key necessary condition (WHY this search is fast):
Let P be the union of primes dividing x, x+1, x+2. For any p in P, p divides
exactly the same shifted term at x and at y (e.g. p | x+1 and p | y+1), hence
in all cases x ≡ y (mod p). Therefore y ≡ x modulo the square-free modulus

    M = rad(x(x+1)(x+2)).

So any solution must have y = x + t*M for some integer t >= 1.
We can loop over x, compute M, and only test those y in the arithmetic
progression x (mod M) that even fit under the bound.

This is also the clean conceptual difference with k=2:
  k=2 modulus is rad(x(x+1)) = rad(x)*rad(x+1), often much smaller than the
  k=3 modulus, leaving far more "room" for a second solution.
"""

from __future__ import annotations

import argparse
import math
import time
from array import array
from dataclasses import dataclass


def rad_sieve(limit: int) -> array:
    """
    Compute rad(n) for 0..limit using a linear sieve.
    rad(n) = product of distinct primes dividing n (square-free kernel).

    Uses arrays to keep memory reasonable up to ~1e7.
    """
    if limit < 1:
        return array("I", [0]) * (limit + 1)

    spf = array("I", [0]) * (limit + 1)  # smallest prime factor
    rad = array("I", [0]) * (limit + 1)
    rad[1] = 1

    primes: list[int] = []
    primes_append = primes.append

    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
            rad[i] = i
            primes_append(i)

        ri = rad[i]
        si = spf[i]

        for p in primes:
            ip = i * p
            if ip > limit:
                break
            spf[ip] = p
            if p == si:
                # p already divides i, so it contributes no new prime to rad(ip)
                rad[ip] = ri
                break
            rad[ip] = ri * p

    return rad


def _k2_modulus(r0: int, r1: int, cutoff: int) -> int | None:
    # For consecutive integers gcd(x, x+1) = 1, so primes are disjoint and
    # M = rad(x(x+1)) = rad(x)*rad(x+1).
    m = r0
    if m > cutoff:
        return None
    m *= r1
    if m > cutoff:
        return None
    return m


def _k3_modulus(x: int, r0: int, r1: int, r2: int, cutoff: int) -> int | None:
    # For three consecutive integers:
    # - rad(x+1) is coprime to rad(x) and rad(x+2).
    # - rad(x) and rad(x+2) overlap only at 2 (when x is even).
    #
    # So M = rad(x(x+1)(x+2)) is the product of all distinct primes appearing.
    # We compute it with early-abort so we don't build huge integers when
    # M obviously exceeds the remaining search window (cutoff).
    m = r0
    if (x & 1) == 0:
        # Remove one copy of prime 2 from the overlap between r0 and r2.
        m //= 2
    if m > cutoff:
        return None
    m *= r1
    if m > cutoff:
        return None
    m *= r2
    if m > cutoff:
        return None
    return m


@dataclass(frozen=True)
class Witness:
    x: int
    y: int
    t: int
    modulus: int


def search_k2(bound: int, rad: array, *, min_gap: int = 1, max_witnesses: int = 20) -> list[Witness]:
    """
    Search for k=2 witnesses up to bound:
      rad(x)=rad(y), rad(x+1)=rad(y+1)
    using the modulus y = x + t*rad(x(x+1)).
    """
    start = time.time()
    results: list[Witness] = []
    tested_y = 0
    x_with_room = 0

    for x in range(1, bound):
        r0 = rad[x]
        r1 = rad[x + 1]
        room = bound - x
        m = _k2_modulus(r0, r1, room)
        if m is None:
            continue

        x_with_room += 1
        t_start = 1 if m >= min_gap else (min_gap + m - 1) // m
        max_t = room // m
        for t in range(t_start, max_t + 1):
            tested_y += 1
            y = x + t * m
            if rad[y] == r0 and rad[y + 1] == r1:
                results.append(Witness(x=x, y=y, t=t, modulus=m))
                if len(results) >= max_witnesses:
                    elapsed = time.time() - start
                    print(
                        f"k=2: hit max_witnesses={max_witnesses} (x_with_room={x_with_room:,}, tested_y={tested_y:,}, {elapsed:.1f}s)"
                    )
                    return results

    elapsed = time.time() - start
    print(f"k=2: done (x_with_room={x_with_room:,}, tested_y={tested_y:,}, {elapsed:.1f}s)")
    return results


def search_k3(bound: int, rad: array, *, min_gap: int = 30, max_witnesses: int = 5) -> list[Witness]:
    """
    Search for k=3 witnesses up to bound:
      rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2)
    using the necessary modulus y = x + t*rad(x(x+1)(x+2)).

    min_gap defaults to the known constraint |x-y| >= 30.
    """
    start = time.time()
    results: list[Witness] = []
    tested_y = 0
    x_with_room = 0
    best_modulus: tuple[int, int] | None = None  # (M, x)

    for x in range(4, bound + 1):
        r0 = rad[x]
        r1 = rad[x + 1]
        r2 = rad[x + 2]

        room = bound - x
        m = _k3_modulus(x, r0, r1, r2, room)
        if m is None:
            continue

        x_with_room += 1
        if best_modulus is None or m < best_modulus[0]:
            best_modulus = (m, x)

        t_start = 1 if m >= min_gap else (min_gap + m - 1) // m
        max_t = room // m
        for t in range(t_start, max_t + 1):
            tested_y += 1
            y = x + t * m
            if rad[y] == r0 and rad[y + 1] == r1 and rad[y + 2] == r2:
                results.append(Witness(x=x, y=y, t=t, modulus=m))
                print(f"k=3 witness: x={x}, y={y}, gap={y-x}, t={t}, M={m}")
                if len(results) >= max_witnesses:
                    elapsed = time.time() - start
                    print(
                        f"k=3: hit max_witnesses={max_witnesses} (x_with_room={x_with_room:,}, tested_y={tested_y:,}, {elapsed:.1f}s)"
                    )
                    return results

        if x % 1_000_000 == 0:
            elapsed = time.time() - start
            bm = "" if best_modulus is None else f", best_M={best_modulus[0]:,} at x={best_modulus[1]:,}"
            print(
                f"k=3: x={x:,}/{bound:,} (x_with_room={x_with_room:,}, tested_y={tested_y:,}, {elapsed:.1f}s{bm})"
            )

    elapsed = time.time() - start
    bm = "" if best_modulus is None else f", best_M={best_modulus[0]:,} at x={best_modulus[1]:,}"
    print(f"k=3: done (x_with_room={x_with_room:,}, tested_y={tested_y:,}, {elapsed:.1f}s{bm})")
    return results


def factorint(n: int) -> list[tuple[int, int]]:
    """Tiny helper for human-readable output (trial division up to sqrt(n))."""
    if n <= 1:
        return []
    out: list[tuple[int, int]] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out.append((d, e))
        d = 3 if d == 2 else d + 2
    if n > 1:
        out.append((n, 1))
    return out


def _fmt_factor(f: list[tuple[int, int]]) -> str:
    if not f:
        return "1"
    parts = []
    for p, e in f:
        parts.append(str(p) if e == 1 else f"{p}^{e}")
    return " * ".join(parts)


def radical_via_factorint(n: int) -> int:
    """Compute rad(n) from the tiny trial-division helper for report mode."""
    out = 1
    for p, _ in factorint(n):
        out *= p
    return out


def report_k2_power_of_two_family(samples: int) -> None:
    """
    Report the classical infinite k=2 family

        x = 2^n - 2,   y = x(x+2),

    and show the built-in obstruction at the third shift.

    WHY this matters:
    - rad(y) = rad(x), because x is even and x+2 is a pure power of 2.
    - y+1 = x(x+2)+1 = (x+1)^2, so rad(y+1) = rad(x+1).
    - But x+2 = 2^n has radical 2, whereas y+2 = (x+1)^2 + 1 is > 2 and
      congruent to 2 mod 8, so it has an odd prime factor. This blocks any
      extension of the family from k=2 to k=3.
    """
    if samples <= 0:
        return

    print("\nClassical k=2 family and its k=3 obstruction:")
    for n in range(2, 2 + samples):
        x = (1 << n) - 2
        y = x * (x + 2)
        rx2 = radical_via_factorint(x + 2)
        ry2 = radical_via_factorint(y + 2)
        odd_cofactor = (y + 2) // 2
        print(
            f"- n={n}: x={x}, y={y}; "
            f"rad(x)={radical_via_factorint(x)}=rad(y)={radical_via_factorint(y)}, "
            f"rad(x+1)={radical_via_factorint(x+1)}=rad(y+1)={radical_via_factorint(y+1)}, "
            f"but rad(x+2)={rx2} and rad(y+2)={ry2} (odd cofactor {(odd_cofactor)})"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Search for Erdos 850 (k=3) witnesses via radical modulus pruning.")
    parser.add_argument("--bound", type=int, default=1_000_000, help="Search bound for x,y (default: 1e6).")
    parser.add_argument("--k", type=int, choices=(2, 3), default=3, help="k=2 or k=3 (default: 3).")
    parser.add_argument(
        "--min-gap",
        type=int,
        default=None,
        help="Require |x-y| >= min_gap (default: 30 for k=3, 1 for k=2).",
    )
    parser.add_argument("--max-witnesses", type=int, default=20, help="Stop after this many witnesses.")
    parser.add_argument(
        "--family-samples",
        type=int,
        default=0,
        help="Print this many samples from the classical infinite k=2 family x=2^n-2, y=x(x+2).",
    )
    args = parser.parse_args()

    bound = args.bound
    k = args.k
    min_gap = args.min_gap if args.min_gap is not None else (30 if k == 3 else 1)

    if bound < 10:
        raise SystemExit("bound too small")

    limit = bound + k  # need radicals up to y+k
    print(f"Computing rad(n) for n <= {limit:,} ...")
    t0 = time.time()
    rad = rad_sieve(limit)
    print(f"rad sieve done in {time.time() - t0:.1f}s")

    if k == 2:
        witnesses = search_k2(bound, rad, min_gap=min_gap, max_witnesses=args.max_witnesses)
    else:
        witnesses = search_k3(bound, rad, min_gap=min_gap, max_witnesses=args.max_witnesses)

    if not witnesses:
        print("No witnesses found.")
        report_k2_power_of_two_family(args.family_samples)
        return

    print("\nWitnesses (factored):")
    for w in witnesses:
        x, y = w.x, w.y
        print(
            f"- x={x}, y={y}, gap={y-x}, t={w.t}, M={w.modulus} :: "
            f"x={_fmt_factor(factorint(x))}, x+1={_fmt_factor(factorint(x+1))}, x+2={_fmt_factor(factorint(x+2))}; "
            f"y={_fmt_factor(factorint(y))}, y+1={_fmt_factor(factorint(y+1))}, y+2={_fmt_factor(factorint(y+2))}"
        )

    report_k2_power_of_two_family(args.family_samples)


if __name__ == "__main__":
    main()
