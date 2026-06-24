#!/usr/bin/env python3
"""
Erdős Problem 203 exploration (coverings for 2^k * 3^l * m + 1).

Goal (open problem): find m with gcd(m,6)=1 such that 2^k * 3^l * m + 1 is never prime for k,l>=0.

What we can do computationally:
  1) For primes p>3, compute ord_p(2), ord_p(3) and n_p := lcm(ord_p(2), ord_p(3)).
  2) For each p, compute which (k mod ord_p(2), l mod ord_p(3)) classes force
     p | (2^k 3^l m + 1) for a chosen residue m ≡ r (mod p).
  3) Attempt finite-modulus coverings: choose finitely many primes and residues (mod those primes),
     then verify coverage on the fundamental domain K×L where K=lcm(ord_p(2)), L=lcm(ord_p(3)).

This does NOT resolve the open problem; it helps search for candidate covering systems in feasible boxes.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

import numpy as np
import sympy as sp


def lcm(a: int, b: int) -> int:
    return a // math.gcd(a, b) * b


def ord_mod(a: int, p: int) -> int:
    """Multiplicative order of a mod prime p (assumes gcd(a,p)=1)."""
    return int(sp.n_order(a, p))


def inv_mod(a: int, p: int) -> int:
    """Modular inverse of a mod p (p prime, a nonzero)."""
    # Python's pow(a, -1, p) is fine, but be explicit for clarity.
    return pow(a, p - 2, p)


@dataclass(frozen=True)
class PrimeOrders:
    p: int
    ord2: int
    ord3: int

    @property
    def subgroup_size(self) -> int:
        # In (Z/pZ)^* cyclic, |<2,3>| = lcm(ord_p(2), ord_p(3)).
        return lcm(self.ord2, self.ord3)


def prime_orders(primes: Iterable[int]) -> List[PrimeOrders]:
    out: List[PrimeOrders] = []
    for p in primes:
        if p <= 3 or not sp.isprime(p):
            raise ValueError(f"Expected prime p>3, got {p}")
        out.append(PrimeOrders(p=p, ord2=ord_mod(2, p), ord3=ord_mod(3, p)))
    return out


def classes_for_prime(p: int) -> Tuple[PrimeOrders, Dict[int, List[Tuple[int, int]]]]:
    """
    For a prime p, return:
      - orders (ord2, ord3)
      - mapping r -> list of (k_mod_ord2, l_mod_ord3) pairs such that
            m ≡ r (mod p)  =>  p | (2^k 3^l m + 1)
        for all k,l in that residue class.
    """
    o = prime_orders([p])[0]
    ord2, ord3 = o.ord2, o.ord3

    pow2 = [1] * ord2
    for i in range(1, ord2):
        pow2[i] = (pow2[i - 1] * 2) % p
    pow3 = [1] * ord3
    for j in range(1, ord3):
        pow3[j] = (pow3[j - 1] * 3) % p

    table: Dict[int, List[Tuple[int, int]]] = {}
    for k in range(ord2):
        for l_ in range(ord3):
            v = (pow2[k] * pow3[l_]) % p
            r = (-inv_mod(v, p)) % p
            table.setdefault(r, []).append((k, l_))
    return o, table


def density_lower_bound(orders: List[PrimeOrders]) -> float:
    """
    Necessary condition heuristic:
      each prime p used with a single residue m (mod p) covers exactly a 1/n_p fraction
      of (k,l) residue classes in its own period, where n_p = |<2,3>| = lcm(ord2, ord3).

    Therefore we need sum_p 1/n_p >= 1 for *any* hope of a disjoint-ish covering.
    (Still far from sufficient in practice.)
    """
    return float(sum(1 / o.subgroup_size for o in orders))


def fundamental_domain(orders: List[PrimeOrders]) -> Tuple[int, int]:
    K = 1
    L = 1
    for o in orders:
        K = lcm(K, o.ord2)
        L = lcm(L, o.ord3)
    return K, L


def required_residue_grid(p: int, K: int, L: int) -> np.ndarray:
    """
    Return req[k,l] = r in {1,...,p-1} such that
        m ≡ r (mod p)  =>  p | (2^k 3^l m + 1)
    for that (k,l).  Computed on 0<=k<K, 0<=l<L.

    Why this helps: choosing a single residue r_p for each prime p turns the covering
    condition into: for every (k,l) cell, at least one chosen prime has req_p[k,l] == r_p.
    """
    o = prime_orders([p])[0]
    ord2, ord3 = o.ord2, o.ord3
    if K % ord2 or L % ord3:
        raise ValueError(f"K={K} must be multiple of ord2={ord2}, L={L} multiple of ord3={ord3}")

    pow2_cycle = np.empty(ord2, dtype=np.int64)
    pow2_cycle[0] = 1
    for i in range(1, ord2):
        pow2_cycle[i] = (pow2_cycle[i - 1] * 2) % p
    pow2 = pow2_cycle[np.arange(K) % ord2]

    pow3_cycle = np.empty(ord3, dtype=np.int64)
    pow3_cycle[0] = 1
    for j in range(1, ord3):
        pow3_cycle[j] = (pow3_cycle[j - 1] * 3) % p
    pow3 = pow3_cycle[np.arange(L) % ord3]

    inv = np.zeros(p, dtype=np.int64)
    for a in range(1, p):
        inv[a] = pow(a, p - 2, p)

    v = (pow2[:, None] * pow3[None, :]) % p
    req = (-inv[v]) % p
    # fits in uint16 for the primes we typically look at; keep it compact.
    return req.astype(np.uint16)


def crt_combine(residues: List[Tuple[int, int]]) -> int:
    """Given [(r mod p), ...] with pairwise-coprime primes p, return smallest nonnegative m."""
    mods = [p for p, _ in residues]
    rems = [r for _, r in residues]
    m, mod = sp.ntheory.modular.crt(mods, rems)
    if m is None:
        raise ValueError("CRT failed (inconsistent residues?)")
    return int(m % mod)


def greedy_cover(primes: List[int], max_cells: int) -> None:
    orders = prime_orders(primes)
    K, L = fundamental_domain(orders)
    cells = K * L
    print(f"K={K} L={L} cells={cells}")
    print(f"Density lower bound sum 1/n_p = {density_lower_bound(orders):.6f}")

    if cells > max_cells:
        raise SystemExit(f"Refusing to allocate {cells} cells (> {max_cells}). Increase --max-cells.")

    # Precompute required residue grids for each prime.
    req: Dict[int, np.ndarray] = {}
    for o in orders:
        req[o.p] = required_residue_grid(o.p, K, L).ravel()

    uncovered = np.ones(cells, dtype=bool)
    chosen: List[Tuple[int, int, int]] = []  # (p, r, newly_covered)
    unused = set(primes)

    step = 0
    while unused and uncovered.any():
        step += 1
        best = None
        for p in sorted(unused):
            vals = req[p][uncovered]
            counts = np.bincount(vals, minlength=p)
            r_best = int(counts[1:].argmax() + 1)
            score = int(counts[r_best])
            if best is None or score > best[0]:
                best = (score, p, r_best)
        assert best is not None
        score, p, r_best = best
        if score == 0:
            break

        mask = req[p] == r_best
        newly = int(np.count_nonzero(uncovered & mask))
        uncovered &= ~mask
        unused.remove(p)
        chosen.append((p, r_best, newly))
        print(f"step {step}: p={p} r={r_best} newly={newly} remaining={int(uncovered.sum())}")

    if uncovered.any():
        print(f"FAILED: remaining uncovered cells = {int(uncovered.sum())} (out of {cells})")
        return

    residues = [(p, r) for (p, r, _) in chosen]
    m0 = crt_combine(residues)
    # adjust to be coprime to 6 (always possible since product of odd primes !=3 is coprime to 6)
    P = 1
    for p, _ in residues:
        P *= p
    m = m0
    for t in range(6):
        if math.gcd(m, 6) == 1:
            break
        m += P
    print("SUCCESS")
    print(f"m ≡ {m0} (mod {P})")
    print(f"One choice with gcd(m,6)=1: m = {m}")
    print("Residues (p -> m mod p):")
    for p, r, _ in chosen:
        print(f"  {p}: {r}")


@dataclass(frozen=True)
class ModCoverPrime:
    """
    Precomputation for the special case where we work on an N×N grid and only use primes p
    with ord_p(2) | N and ord_p(3) | N.  Then the divisibility condition depends only on
    (k mod n, l mod n) where n = lcm(ord_p(2), ord_p(3)) and n | N.

    We represent 2 = g^a, 3 = g^b in the unique subgroup of (Z/pZ)^* of order n.
    For each (i,j) in Z_n×Z_n we have 2^i 3^j = g^(a*i + b*j).
    """

    p: int
    n: int
    a: int
    b: int
    exp_to_val: np.ndarray  # length n, exp_to_val[e] = g^e mod p
    gamma_flat: np.ndarray  # length n*n, gamma_flat[i*n+j] = (a*i + b*j) mod n


def _mod_cover_prime(p: int, N: int) -> ModCoverPrime:
    o = prime_orders([p])[0]
    if N % o.ord2 or N % o.ord3:
        raise ValueError(f"p={p} does not satisfy ord2|N and ord3|N for N={N}")
    n = o.subgroup_size
    if N % n:
        raise ValueError(f"Expected n|N, got n={n} N={N} for p={p}")

    g0 = int(sp.primitive_root(p))
    g = pow(g0, (p - 1) // n, p)  # generator of unique subgroup of order n

    exp_to_val = np.empty(n, dtype=np.int64)
    val_to_exp: Dict[int, int] = {}
    x = 1
    for e in range(n):
        exp_to_val[e] = x
        val_to_exp[int(x)] = e
        x = (x * g) % p

    a = val_to_exp[2 % p]
    b = val_to_exp[3 % p]

    i = np.arange(n, dtype=np.int64)
    j = np.arange(n, dtype=np.int64)
    gamma_flat = (((a * i)[:, None] + (b * j)[None, :]) % n).astype(np.int32).ravel()
    return ModCoverPrime(p=p, n=n, a=a, b=b, exp_to_val=exp_to_val, gamma_flat=gamma_flat)


def _apply_mod_prime(uncovered: np.ndarray, d: ModCoverPrime, gamma: int) -> None:
    """
    Mark as covered all (k,l) in [0..N-1]^2 satisfying a*k + b*l ≡ gamma (mod n).

    We avoid building a full mask; instead we write strided slices. This touches exactly N^2/n cells.
    """
    N = uncovered.shape[0]
    n = d.n
    a = d.a
    b = d.b

    dg = math.gcd(a, n)
    a1 = a // dg
    n1 = n // dg
    inv_a1 = pow(a1, -1, n1)

    for l_res in range(n):
        rhs = (gamma - b * l_res) % n
        if rhs % dg:
            continue
        rhs1 = rhs // dg
        k0 = (inv_a1 * rhs1) % n1
        for t in range(dg):
            k_res = k0 + n1 * t
            uncovered[k_res::n, l_res::n] = False


def mod_search_cover(N: int, prime_limit: int, trials: int, seed: int) -> None:
    """
    Attempt a covering on the finite grid (k,l) mod N with primes satisfying ord_p(2)|N and ord_p(3)|N.

    Why this is interesting: if one could cover the full Z×Z, one would in particular get a covering
    on every such finite fundamental domain.  Failure here is not a proof of impossibility, but it
    gives quantitative feedback on how far naive coverings are from succeeding.
    """
    primes: List[int] = []
    for p in sp.primerange(5, prime_limit + 1):
        if N % ord_mod(2, p) == 0 and N % ord_mod(3, p) == 0:
            primes.append(int(p))

    if not primes:
        raise SystemExit("No primes found (increase --prime-limit or choose different N).")

    orders = prime_orders(primes)
    print(f"N={N} candidate primes={len(primes)} max_p={max(primes)}")
    print(f"Density lower bound sum 1/n_p = {density_lower_bound(orders):.6f}")

    meta = [_mod_cover_prime(p, N) for p in primes]
    # Heuristic order: cover with largest-density primes first (small n).
    meta.sort(key=lambda d: d.n)

    rng = np.random.default_rng(seed)
    best_remaining = N * N + 1
    best_choice: List[Tuple[int, int]] = []

    for t in range(trials):
        uncovered = np.ones((N, N), dtype=np.bool_)
        choice: List[Tuple[int, int]] = []  # (p, r=m mod p)

        for d in meta:
            n = d.n
            q = N // n
            counts = uncovered.reshape(q, n, q, n).sum(axis=(0, 2)).astype(np.int64)
            dist = np.bincount(d.gamma_flat, weights=counts.ravel(), minlength=n)
            best = np.flatnonzero(dist == dist.max())
            gamma = int(rng.choice(best))

            tval = int(d.exp_to_val[gamma])
            r = (-inv_mod(tval, d.p)) % d.p
            choice.append((d.p, r))
            _apply_mod_prime(uncovered, d, gamma)

        remaining = int(uncovered.sum())
        if remaining < best_remaining:
            best_remaining = remaining
            best_choice = choice
        print(f"trial {t+1:>3}/{trials}: remaining={remaining}")
        if remaining == 0:
            break

    print(f"best remaining={best_remaining}")
    if best_remaining != 0:
        return

    m0 = crt_combine(best_choice)
    P = 1
    for p, _ in best_choice:
        P *= p
    m = m0
    for _ in range(6):
        if math.gcd(m, 6) == 1:
            break
        m += P
    print("SUCCESS (finite N×N covering)")
    print(f"m ≡ {m0} (mod {P})")
    print(f"One choice with gcd(m,6)=1: m = {m}")


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    ap_orders = sub.add_parser("orders", help="Print ord_p(2), ord_p(3) for primes")
    ap_orders.add_argument("--prime-limit", type=int, default=200)
    ap_orders.add_argument("--primes", type=str, default="")

    ap_classes = sub.add_parser("classes", help="Show residue-class mapping for a single prime p")
    ap_classes.add_argument("--p", type=int, required=True)

    ap_greedy = sub.add_parser("greedy", help="Greedy finite-modulus covering search")
    ap_greedy.add_argument("--primes", type=str, required=True, help="Comma-separated primes >3")
    ap_greedy.add_argument("--max-cells", type=int, default=40_000_000)

    ap_mod = sub.add_parser("mod-search", help="Search coverings on an N×N exponent grid")
    ap_mod.add_argument("--N", type=int, default=5040)
    ap_mod.add_argument("--prime-limit", type=int, default=50_000)
    ap_mod.add_argument("--trials", type=int, default=10)
    ap_mod.add_argument("--seed", type=int, default=0)

    args = ap.parse_args()

    if args.cmd == "orders":
        if args.primes:
            primes = [int(x) for x in args.primes.split(",") if x.strip()]
        else:
            primes = list(sp.primerange(5, args.prime_limit + 1))
        orders = prime_orders(primes)
        for o in sorted(orders, key=lambda t: t.p):
            print(f"p={o.p:5d} ord2={o.ord2:5d} ord3={o.ord3:5d} n=lcm={o.subgroup_size:5d} 1/n={1/o.subgroup_size:.6f}")
        print(f"sum 1/n = {density_lower_bound(orders):.6f}")
        return

    if args.cmd == "classes":
        o, table = classes_for_prime(args.p)
        ker = (o.ord2 * o.ord3) // o.subgroup_size
        print(f"p={o.p} ord2={o.ord2} ord3={o.ord3} n=lcm={o.subgroup_size} kernel_size={ker}")
        # show the largest buckets first
        items = sorted(table.items(), key=lambda kv: (-len(kv[1]), kv[0]))
        for r, pairs in items[:20]:
            print(f"m ≡ {r:>4} (mod {o.p}) covers {len(pairs)} residue-pairs; e.g. {pairs[:8]}")
        print(f"distinct residues r: {len(table)} (should be n={o.subgroup_size})")
        return

    if args.cmd == "greedy":
        primes = [int(x) for x in args.primes.split(",") if x.strip()]
        greedy_cover(primes, max_cells=args.max_cells)
        return

    if args.cmd == "mod-search":
        mod_search_cover(N=int(args.N), prime_limit=int(args.prime_limit), trials=int(args.trials), seed=int(args.seed))
        return


if __name__ == "__main__":
    main()
