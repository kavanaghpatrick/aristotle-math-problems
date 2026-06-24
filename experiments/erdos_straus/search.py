#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from collections import Counter
from dataclasses import dataclass
from math import isqrt


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if is_prime[p]:
            step = p
            start = p * p
            is_prime[start : limit + 1 : step] = b"\x00" * (((limit - start) // step) + 1)
    return [i for i in range(2, limit + 1) if is_prime[i]]


@dataclass(frozen=True)
class Solution:
    p: int
    x: int
    y: int
    z: int
    a: int  # a = 4x - p
    method: str  # "typeI" or "divisor"
    d: int | None = None
    e: int | None = None
    u: int | None = None  # witness divisor of (p x)^2


def check_solution(p: int, x: int, y: int, z: int) -> bool:
    # 4/p = 1/x + 1/y + 1/z  <=>  4xyz = p(xy + yz + zx)
    left = 4 * x * y * z
    right = p * (x * y + y * z + z * x)
    return left == right


def factorize(n: int) -> dict[int, int]:
    """Trial division; fast enough for x ≈ p/4 in our ranges."""
    if n <= 1:
        return {}
    out: dict[int, int] = {}
    while n % 2 == 0:
        out[2] = out.get(2, 0) + 1
        n //= 2
    d = 3
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def iter_divisors_from_factorization(factors: dict[int, int]):
    items = list(factors.items())

    def rec(i: int, acc: int):
        if i == len(items):
            yield acc
            return
        prime, exp = items[i]
        mul = 1
        for _ in range(exp + 1):
            yield from rec(i + 1, acc * mul)
            mul *= prime

    yield from rec(0, 1)


def try_type_i(p: int, a: int, x: int) -> Solution | None:
    # Type I: take 1/y + 1/z = (d+e)/(p x) with d,e|x and d+e=a.
    for d in range(1, (a // 2) + 1):
        e = a - d
        if x % d != 0 or x % e != 0:
            continue
        y = p * (x // d)
        z = p * (x // e)
        if check_solution(p, x, y, z):
            return Solution(p=p, x=x, y=y, z=z, a=a, method="typeI", d=d, e=e)
    return None


def try_divisor_method(p: int, a: int, x: int) -> Solution | None:
    # General 2-term expansion via (a y - b)(a z - b) = b^2 with b = p x.
    b = p * x
    b2 = b * b

    fb = factorize(x)
    fb[p] = fb.get(p, 0) + 1
    fb2 = {q: 2 * e for q, e in fb.items()}

    for u in iter_divisors_from_factorization(fb2):
        if (b + u) % a != 0:
            continue
        v = b2 // u
        if (b + v) % a != 0:
            continue
        y = (b + u) // a
        z = (b + v) // a
        if y <= 0 or z <= 0:
            continue
        if check_solution(p, x, y, z):
            return Solution(p=p, x=x, y=y, z=z, a=a, method="divisor", u=u)
    return None


def find_solution(p: int, a_max: int) -> Solution | None:
    """
    Scan small a = 4x - p with x = (p + a)/4 close to p/4.

    For fixed x, let A = a and B = p x. We need

        A/B = 1/y + 1/z

    which is equivalent to

        (A y - B)(A z - B) = B^2.

    So it suffices to find a divisor u|B^2 with
        A | (B + u)  and  A | (B + B^2/u),
    then set y = (B + u)/A, z = (B + B^2/u)/A.
    """
    for a in range(3, a_max + 1, 4):
        if (p + a) % 4 != 0:
            continue
        x = (p + a) // 4
        if x <= 0:
            continue
        sol = try_type_i(p, a, x)
        if sol is not None:
            return sol
        sol = try_divisor_method(p, a, x)
        if sol is not None:
            return sol
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description="Erdos–Straus search for primes p ≡ 1 (mod 24).")
    parser.add_argument("--limit", type=int, default=1_000_000, help="Search primes up to this bound.")
    parser.add_argument("--amax", type=int, default=400, help="Max a = 4x - p to try in Type I search.")
    parser.add_argument("--show", type=int, default=20, help="Print the first N solutions.")
    parser.add_argument("--csv", type=str, default="", help="Write all solutions to this CSV path.")
    args = parser.parse_args()

    primes = sieve_primes(args.limit)
    targets = [p for p in primes if p % 24 == 1 and p >= 5]

    if not targets:
        print("No primes p ≡ 1 (mod 24) found in range.")
        return 0

    solutions: list[Solution] = []
    missing: list[int] = []

    used_a = Counter()
    used_method = Counter()
    used_pair = Counter()
    used_u_small = Counter()

    for p in targets:
        sol = find_solution(p, args.amax)
        if sol is None:
            missing.append(p)
            continue
        solutions.append(sol)
        used_a[sol.a] += 1
        used_method[sol.method] += 1
        if sol.method == "typeI":
            used_pair[(sol.d, sol.e, sol.a)] += 1
        if sol.u is not None:
            b = p * sol.x
            used_u_small[min(sol.u, (b * b) // sol.u)] += 1

    print(f"Primes p ≡ 1 (mod 24) up to {args.limit}: {len(targets)}")
    print(f"Solutions found with a ≤ {args.amax}: {len(solutions)}")
    print(f"Missing: {len(missing)}")

    if missing:
        print("First missing primes:", ", ".join(map(str, missing[: min(20, len(missing))])))

    if solutions:
        print(f"Methods used: {dict(used_method)}")
        worst = sorted(solutions, key=lambda s: s.a, reverse=True)[:10]
        print(f"Max a used: {worst[0].a}")
        print()
        print("First solutions (p, x, y, z) with x=(p+a)/4:")
        for sol in solutions[: args.show]:
            x, y, z = sorted([sol.x, sol.y, sol.z])
            extras = []
            if sol.method == "typeI":
                extras.append(f"(d,e)=({sol.d},{sol.e})")
            if sol.u is not None:
                extras.append(f"u={sol.u}")
            extra = ("  " + "  ".join(extras)) if extras else ""
            print(f"p={sol.p:>8}  (x,y,z)=({x}, {y}, {z})  a={sol.a}  method={sol.method}{extra}")

        print()
        print("Most common a values:")
        for a, cnt in used_a.most_common(12):
            print(f"a={a:>4}: {cnt}")

        print()
        print("Largest a values (with one example p):")
        for sol in worst:
            print(f"a={sol.a:>4}  p={sol.p}")

        print()
        if used_pair:
            print("Most common (d,e,a) Type I patterns:")
            for (d, e, a), cnt in used_pair.most_common(12):
                print(f"(d,e,a)=({d},{e},{a}): {cnt}")

        if used_u_small:
            print()
            print("Most common small witnesses min(u, (px)^2/u):")
            for u, cnt in used_u_small.most_common(12):
                print(f"u={u:>8}: {cnt}")

    if args.csv:
        with open(args.csv, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["p", "x", "y", "z", "a", "method", "d", "e", "u"])
            for sol in solutions:
                w.writerow([sol.p, sol.x, sol.y, sol.z, sol.a, sol.method, sol.d, sol.e, sol.u])
        print()
        print(f"Wrote {len(solutions)} solutions to {args.csv}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
