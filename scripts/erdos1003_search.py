"""
Erdos Problem 1003: search for n with phi(n) = phi(n+1).

The script has two jobs:
1. Exhaustively find all hits up to a bound using a linear totient sieve.
2. Summarize the structure of the hits and test the simplest CRT-based
   construction attempts.

The CRT analysis is intentionally modest. It studies the shape

    n = A * u,   n + 1 = B * v,

with gcd(A, B) = 1 and u, v prime. CRT puts n in one residue class mod AB,
so u and v become linear forms in one parameter t. The totient equality is
also linear in t, so for fixed A, B there is at most one possible t unless a
degenerate identity holds. That gives a clean obstruction to "easy" infinite
families of this type.
"""

from __future__ import annotations

import argparse
import math
import time
from array import array
from collections import Counter
from dataclasses import dataclass


def linear_phi_sieve(limit: int) -> tuple[array, array]:
    """
    Compute phi(n) and spf(n) for 0 <= n <= limit by a linear sieve.

    WHY this version: it keeps the search fast enough for 10^7 in plain Python
    while also giving us smallest-prime-factor data for the structural report.
    """
    phi = array("I", [0]) * (limit + 1)
    spf = array("I", [0]) * (limit + 1)
    primes: list[int] = []

    if limit >= 1:
        phi[1] = 1

    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
            phi[i] = i - 1
            primes.append(i)

        for p in primes:
            ip = i * p
            if ip > limit:
                break
            spf[ip] = p
            if i % p == 0:
                phi[ip] = phi[i] * p
                break
            phi[ip] = phi[i] * (p - 1)

    return phi, spf


def factor_with_spf(n: int, spf: array) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


def omega_distinct(n: int, spf: array) -> int:
    count = 0
    while n > 1:
        p = spf[n]
        count += 1
        while n % p == 0:
            n //= p
    return count


def is_prime(n: int, spf: array) -> bool:
    return n >= 2 and spf[n] == n


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def format_factorization(n: int, spf: array) -> str:
    if n <= 1:
        return "1"
    pieces = []
    for p, e in factor_with_spf(n, spf):
        pieces.append(str(p) if e == 1 else f"{p}^{e}")
    return " * ".join(pieces)


def find_hits(limit: int, phi: array) -> list[int]:
    return [n for n in range(1, limit + 1) if phi[n] == phi[n + 1]]


def consecutive_runs(hits: list[int]) -> list[tuple[int, int]]:
    if not hits:
        return []
    runs: list[tuple[int, int]] = []
    start = hits[0]
    prev = hits[0]
    for n in hits[1:]:
        if n == prev + 1:
            prev = n
            continue
        runs.append((start, prev))
        start = prev = n
    runs.append((start, prev))
    return runs


def two_adic_valuation(n: int) -> int:
    v = 0
    while n % 2 == 0 and n > 0:
        n //= 2
        v += 1
    return v


@dataclass(frozen=True)
class CRTCandidate:
    a: int
    b: int
    t: int
    n: int
    u: int
    v: int
    phi_n: int


def egcd(a: int, b: int) -> tuple[int, int, int]:
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)


def crt_pair(a1: int, m1: int, a2: int, m2: int) -> tuple[int, int]:
    g, x, _ = egcd(m1, m2)
    if g != 1:
        raise ValueError("moduli must be coprime")
    mod = m1 * m2
    value = (a1 + (a2 - a1) * x * m1) % mod
    return value, mod


def phi_from_factors(factors: list[tuple[int, int]]) -> int:
    value = 1
    for p, e in factors:
        value *= (p - 1) * (p ** (e - 1))
    return value


def phi_via_spf(n: int, spf: array) -> int:
    return phi_from_factors(factor_with_spf(n, spf))


def crt_one_prime_tail_candidates(kernel_limit: int, spf: array) -> list[CRTCandidate]:
    """
    Enumerate small fixed kernels A, B for the shape

        n = A * u,    n + 1 = B * v,

    where u, v are prime. For each coprime pair A, B the totient equality gives
    a single linear equation in t, so there is at most one candidate.
    """
    out: list[CRTCandidate] = []
    phi_cache = [0] * (kernel_limit + 1)
    for n in range(1, kernel_limit + 1):
        phi_cache[n] = phi_via_spf(n, spf)
    spf_limit = len(spf) - 1

    for a in range(2, kernel_limit + 1):
        phi_a = phi_cache[a]
        for b in range(2, kernel_limit + 1):
            if math.gcd(a, b) != 1:
                continue

            n0, mod = crt_pair(0, a, -1 % b, b)
            u0 = n0 // a
            v0 = (n0 + 1) // b

            denom = phi_a * b - phi_cache[b] * a
            if denom == 0:
                continue

            numer = phi_cache[b] * (v0 - 1) - phi_a * (u0 - 1)
            if numer % denom != 0:
                continue

            t = numer // denom
            if t < 0:
                continue

            n = n0 + t * mod
            if n <= 0 or n + 1 > spf_limit:
                continue

            u = n // a
            v = (n + 1) // b
            if u <= 1 or v <= 1:
                continue
            if n % a != 0 or (n + 1) % b != 0:
                continue
            if math.gcd(u, a) != 1 or math.gcd(v, b) != 1:
                continue
            if not is_prime(u, spf) or not is_prime(v, spf):
                continue

            phi_n = phi_a * (u - 1)
            if phi_n != phi_cache[b] * (v - 1):
                continue

            out.append(CRTCandidate(a=a, b=b, t=t, n=n, u=u, v=v, phi_n=phi_n))

    out.sort(key=lambda item: item.n)
    return out


def structural_report(limit: int, hits: list[int], phi: array, spf: array) -> None:
    print(f"Search bound: {limit:,}")
    print(f"Hit count: {len(hits):,}")
    if not hits:
        return

    print(f"First hits: {hits[:15]}")
    print(f"Last hits:  {hits[-15:]}")

    odd_hits = sum(n % 2 == 1 for n in hits)
    power2_next = [n for n in hits if is_power_of_two(n + 1)]
    power2_prev = [n for n in hits if is_power_of_two(n)]
    runs = [run for run in consecutive_runs(hits) if run[0] != run[1]]

    print(f"Odd n hits: {odd_hits:,} / {len(hits):,}")
    print(f"Runs of consecutive hits: {runs if runs else 'none'}")
    print(f"n + 1 a power of 2: {power2_next}")
    print(f"n a power of 2:     {power2_prev}")

    omega_n = Counter(omega_distinct(n, spf) for n in hits)
    omega_np1 = Counter(omega_distinct(n + 1, spf) for n in hits)
    print(f"omega(n) distribution:    {dict(sorted(omega_n.items()))}")
    print(f"omega(n+1) distribution:  {dict(sorted(omega_np1.items()))}")

    v2_phi = Counter(two_adic_valuation(phi[n]) for n in hits)
    print(f"v2(phi(n)) distribution:  {dict(sorted(v2_phi.items()))}")

    print("\nSample factorizations:")
    sample = hits[:8]
    if len(hits) > 16:
        sample += hits[-8:]
    for n in sample:
        print(
            f"  n={n:<10} phi={phi[n]:<10} "
            f"n={format_factorization(n, spf):<28} "
            f"n+1={format_factorization(n + 1, spf)}"
        )

    print("\nObserved structure:")
    print("  - Aside from n=1, phi(n)=phi(n+1) is always an even number.")
    print("  - The simplest visible family is n = 2^(2^k) - 1 with n+1 = 2^(2^k).")
    print("    In the computed range this gives n = 3, 15, 255, 65535.")
    print("    These come from the Fermat-product identity")
    print("      (2+1)(2^2+1)...(2^(2^(k-1))+1) = 2^(2^k) - 1,")
    print("    together with phi(2^(2^k)) = 2^(2^k-1).")
    print("  - Most other hits are genuinely mixed-composite cases; they do not sit")
    print("    inside a single obvious parametric progression.")


def print_hit_table(hits: list[int], phi: array, spf: array, show: int) -> None:
    show = min(show, len(hits))
    if show <= 0:
        return
    print("\nDetailed hits:")
    for n in hits[:show]:
        print(
            f"  n={n:<10} phi={phi[n]:<10} "
            f"factors(n)={format_factorization(n, spf):<25} "
            f"factors(n+1)={format_factorization(n + 1, spf)}"
        )


def print_crt_report(kernel_limit: int, spf: array, show: int) -> None:
    print(f"\nCRT one-prime-tail scan with kernels A, B <= {kernel_limit}")
    candidates = crt_one_prime_tail_candidates(kernel_limit, spf)
    print(f"Candidates found: {len(candidates)}")
    for item in candidates[:show]:
        print(
            f"  n={item.n:<8} A={item.a:<4} B={item.b:<4} "
            f"u={item.u:<6} v={item.v:<6} phi={item.phi_n}"
        )
    print("  For fixed coprime A, B this method yields at most one t,")
    print("  so it can explain sporadic examples but not an infinite family.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10_000_000)
    parser.add_argument("--show", type=int, default=20)
    parser.add_argument("--kernel-limit", type=int, default=200)
    parser.add_argument(
        "--skip-crt",
        action="store_true",
        help="Skip the small-kernel CRT scan.",
    )
    args = parser.parse_args()

    sieve_limit = max(args.limit + 1, args.kernel_limit + 10)
    start = time.time()
    phi, spf = linear_phi_sieve(sieve_limit)
    sieve_elapsed = time.time() - start
    print(f"Built phi/spf sieve to {sieve_limit:,} in {sieve_elapsed:.2f}s")

    start = time.time()
    hits = find_hits(args.limit, phi)
    search_elapsed = time.time() - start
    print(f"Scanned n <= {args.limit:,} in {search_elapsed:.2f}s")

    structural_report(args.limit, hits, phi, spf)
    print_hit_table(hits, phi, spf, args.show)

    if not args.skip_crt:
        print_crt_report(args.kernel_limit, spf, args.show)


if __name__ == "__main__":
    main()
