#!/usr/bin/env python3
"""
Erdos problem 672 (l=3): search for coprime n,d such that

    n (n+d) (n+2d) (n+3d) = y^3.

This problem is open in general; this script is for computational exploration:
- exhaustive search up to a bound
- modular "obstruction" checks: does a modulus m rule out solutions?
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass


def iroot3_floor(n: int) -> int:
    """Floor of the real cube-root of n (n >= 0), using integer Newton iteration."""
    if n < 0:
        raise ValueError("iroot3_floor expects n >= 0")
    if n < 2:
        return n

    x = 1 << ((n.bit_length() + 2) // 3)  # 2^{ceil(bitlen/3)}
    while True:
        y = (2 * x + n // (x * x)) // 3
        if y >= x:
            break
        x = y

    while (x + 1) * (x + 1) * (x + 1) <= n:
        x += 1
    while x * x * x > n:
        x -= 1
    return x


def is_perfect_cube(n: int) -> tuple[bool, int]:
    if n < 0:
        return (False, 0)
    y = iroot3_floor(n)
    return (y * y * y == n, y)


def cube_residues(modulus: int) -> set[int]:
    return {pow(a, 3, modulus) for a in range(modulus)}


def ap_product(n: int, d: int) -> int:
    return n * (n + d) * (n + 2 * d) * (n + 3 * d)


@dataclass(frozen=True)
class SearchHit:
    n: int
    d: int
    y: int


def search(
    *,
    max_term: int,
    modulus_filter: int | None,
    stop_after_first: bool,
    progress_every: int,
) -> list[SearchHit]:
    """
    Exhaustive search over positive n,d with n+3d <= max_term and gcd(n,d)=1.
    If modulus_filter is given, we only compute full products when the product
    is a cube residue mod modulus_filter.
    """
    if max_term < 4:
        return []

    cubes_mod = cube_residues(modulus_filter) if modulus_filter else None
    hits: list[SearchHit] = []

    t0 = time.time()
    checked_pairs = 0
    filtered_pairs = 0

    d_max = (max_term - 1) // 3
    for d in range(1, d_max + 1):
        n_max = max_term - 3 * d

        if cubes_mod is not None:
            m = modulus_filter
            r0 = 1 % m
            r1 = (1 + d) % m
            r2 = (1 + 2 * d) % m
            r3 = (1 + 3 * d) % m

        for n in range(1, n_max + 1):
            checked_pairs += 1
            if math.gcd(n, d) != 1:
                if cubes_mod is not None:
                    r0 = (r0 + 1) % m
                    r1 = (r1 + 1) % m
                    r2 = (r2 + 1) % m
                    r3 = (r3 + 1) % m
                continue

            if cubes_mod is not None:
                prod_mod = (r0 * r1) % m
                prod_mod = (prod_mod * r2) % m
                prod_mod = (prod_mod * r3) % m
                if prod_mod not in cubes_mod:
                    filtered_pairs += 1
                    r0 = (r0 + 1) % m
                    r1 = (r1 + 1) % m
                    r2 = (r2 + 1) % m
                    r3 = (r3 + 1) % m
                    continue

            prod = ap_product(n, d)
            ok, y = is_perfect_cube(prod)
            if ok:
                hits.append(SearchHit(n=n, d=d, y=y))
                if stop_after_first:
                    return hits

            if cubes_mod is not None:
                r0 = (r0 + 1) % m
                r1 = (r1 + 1) % m
                r2 = (r2 + 1) % m
                r3 = (r3 + 1) % m

        if progress_every and d % progress_every == 0:
            elapsed = time.time() - t0
            rate = checked_pairs / max(elapsed, 1e-9)
            pct = 100.0 * d / d_max
            filt = filtered_pairs
            print(
                f"[d={d}/{d_max} ({pct:.1f}%)] pairs={checked_pairs:,} "
                f"filtered={filt:,} rate={rate:,.0f}/s hits={len(hits)}"
            )

    return hits


def modulus_obstructs(modulus: int) -> bool:
    """
    Return True if the congruence obstruction holds:
      for all (n,d) mod modulus with gcd(n,d,modulus)=1,
      the product n(n+d)(n+2d)(n+3d) is NOT a cube mod modulus.
    """
    cubes = cube_residues(modulus)
    for n in range(modulus):
        for d in range(modulus):
            if math.gcd(math.gcd(n, d), modulus) != 1:
                continue
            prod = (n * (n + d) * (n + 2 * d) * (n + 3 * d)) % modulus
            if prod in cubes:
                return False
    return True


def find_obstructing_moduli(max_modulus: int) -> list[int]:
    obstructing = []
    for m in range(2, max_modulus + 1):
        if modulus_obstructs(m):
            obstructing.append(m)
    return obstructing


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_search = sub.add_parser("search", help="exhaustive search up to a bound")
    p_search.add_argument("--max-term", type=int, default=5000)
    p_search.add_argument(
        "--mod-filter",
        type=int,
        default=819,
        help="skip pairs whose product is not a cube mod this modulus (0 disables)",
    )
    p_search.add_argument("--stop-after-first", action="store_true")
    p_search.add_argument("--progress-every", type=int, default=250)

    p_mod = sub.add_parser("modcheck", help="check modular obstructions")
    p_mod.add_argument("--modulus", type=int, nargs="*", default=[7, 8, 9, 13])
    p_mod.add_argument("--search-up-to", type=int, default=0)

    args = parser.parse_args()

    if args.cmd == "search":
        modulus_filter = args.mod_filter if args.mod_filter > 0 else None
        hits = search(
            max_term=args.max_term,
            modulus_filter=modulus_filter,
            stop_after_first=args.stop_after_first,
            progress_every=args.progress_every,
        )
        if not hits:
            print("No hits found.")
            return
        for h in hits:
            print(f"n={h.n} d={h.d} y={h.y}")

    if args.cmd == "modcheck":
        for m in args.modulus:
            ok = modulus_obstructs(m)
            print(f"m={m}: {'OBSTRUCTS' if ok else 'allows'}")
        if args.search_up_to and args.search_up_to >= 2:
            obs = find_obstructing_moduli(args.search_up_to)
            print(f"Obstructing moduli <= {args.search_up_to}: {obs}")


if __name__ == "__main__":
    main()
