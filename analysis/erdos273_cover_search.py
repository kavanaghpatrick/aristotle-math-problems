#!/usr/bin/env python3
"""
Construction helper for Erdős problem 273.

Problem 273 asks for a distinct covering system whose moduli are all of the
form p - 1 with p prime and p >= 5. Every such modulus is even, so any
candidate cover splits by parity. After dividing by 2, the problem becomes:

    find two disjoint distinct covering systems with moduli n such that 2n + 1
    is prime.

This script works on that "half-modulus" side because it is the natural search
space for both density tests and construction attempts.

The search strategy is intentionally modest:
1. Build a divisor-closed candidate family.
2. Report the reciprocal-mass and prime-power screens.
3. Try greedy/randomized covers for one side or for two disjoint sides.

It does not claim completeness except in the trivial sense that any returned
cover is verified exactly modulo the common period.
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass
from typing import Iterable


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    p = 3
    while p * p <= n:
        if n % p == 0:
            return False
        p += 2
    return True


def reciprocal_sum(values: Iterable[int]) -> float:
    return sum(1.0 / value for value in values)


def prime_factors(n: int) -> list[tuple[int, int]]:
    factors: list[tuple[int, int]] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exponent = 0
            while n % d == 0:
                n //= d
                exponent += 1
            factors.append((d, exponent))
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors.append((n, 1))
    return factors


def divisors(n: int) -> list[int]:
    result = [1]
    for prime, exponent in prime_factors(n):
        result = [
            divisor * (prime**power)
            for divisor in result
            for power in range(exponent + 1)
        ]
    return sorted(result)


def parse_factorization(text: str) -> int:
    """
    Parse strings such as "2^3*3^2*5*7".
    """
    value = 1
    for chunk in text.split("*"):
        chunk = chunk.strip()
        if not chunk:
            continue
        if "^" in chunk:
            base_text, exp_text = chunk.split("^", 1)
            value *= int(base_text) ** int(exp_text)
        else:
            value *= int(chunk)
    return value


def half_moduli_dividing(period: int) -> list[int]:
    return [d for d in divisors(period) if d >= 2 and is_prime(2 * d + 1)]

@dataclass(frozen=True)
class Cover:
    period: int
    classes: tuple[tuple[int, int], ...]

    @property
    def moduli(self) -> tuple[int, ...]:
        return tuple(modulus for modulus, _ in self.classes)

    def describe(self) -> str:
        parts = [f"{residue} (mod {modulus})" for modulus, residue in self.classes]
        return ", ".join(parts)


def verify_cover(period: int, classes: Iterable[tuple[int, int]]) -> bool:
    for residue in range(period):
        if not any(residue % modulus == class_residue for modulus, class_residue in classes):
            return False
    return True


def uncovered_fraction(period: int, classes: Iterable[tuple[int, int]]) -> float:
    uncovered = 0
    for residue in range(period):
        if not any(residue % modulus == class_residue for modulus, class_residue in classes):
            uncovered += 1
    return uncovered / period


def best_residue(uncovered: list[bool], modulus: int) -> tuple[int, int]:
    counts = [0] * modulus
    for residue, is_uncovered in enumerate(uncovered):
        if is_uncovered:
            counts[residue % modulus] += 1
    best_class = max(range(modulus), key=counts.__getitem__)
    return best_class, counts[best_class]


def greedy_cover(
    period: int,
    candidate_moduli: list[int],
    alpha: float,
    rng: random.Random,
) -> tuple[Cover | None, float]:
    """
    alpha > 0 mildly favors larger moduli. That tends to produce sparser covers,
    which is useful when we are trying to leave room for a second disjoint cover.
    """
    uncovered = [True] * period
    uncovered_count = period
    remaining = candidate_moduli[:]
    rng.shuffle(remaining)
    chosen: list[tuple[int, int]] = []

    while uncovered_count:
        best_choice: tuple[float, float, int, int, int] | None = None
        for modulus in remaining:
            residue, gain = best_residue(uncovered, modulus)
            if gain == 0:
                continue
            score = gain / (modulus**alpha)
            candidate = (score, rng.random(), gain, -modulus, residue)
            if best_choice is None or candidate > best_choice:
                best_choice = candidate
                best_modulus = modulus
                best_residue_class = residue

        if best_choice is None:
            break

        chosen.append((best_modulus, best_residue_class))
        remaining.remove(best_modulus)
        for residue in range(best_residue_class, period, best_modulus):
            if uncovered[residue]:
                uncovered[residue] = False
                uncovered_count -= 1

    cover = Cover(period=period, classes=tuple(sorted(chosen)))
    if uncovered_count == 0 and verify_cover(period, cover.classes):
        return cover, 0.0
    return None, uncovered_count / period


def search_cover(
    period: int,
    candidate_moduli: list[int],
    trials: int,
    seed: int,
) -> tuple[Cover | None, float]:
    best_partial = 1.0
    alphas = [0.0, 0.15, 0.25, 0.35, 0.5, 0.75, 1.0]
    rng = random.Random(seed)

    for _ in range(trials):
        alpha = rng.choice(alphas)
        cover, miss = greedy_cover(period, candidate_moduli, alpha=alpha, rng=rng)
        if cover is not None:
            return cover, 0.0
        best_partial = min(best_partial, miss)

    return None, best_partial


def search_disjoint_pair(
    period: int,
    candidate_moduli: list[int],
    trials: int,
    seed: int,
) -> tuple[tuple[Cover, Cover] | None, tuple[float, float]]:
    rng = random.Random(seed)
    best_miss = (1.0, 1.0)

    for _ in range(trials):
        alpha_first = rng.choice([0.15, 0.25, 0.35, 0.5, 0.75, 1.0])
        first_cover, first_miss = greedy_cover(period, candidate_moduli, alpha=alpha_first, rng=rng)
        if first_cover is None:
            if first_miss < best_miss[0]:
                best_miss = (first_miss, best_miss[1])
            continue

        remaining = [m for m in candidate_moduli if m not in set(first_cover.moduli)]
        alpha_second = rng.choice([0.0, 0.15, 0.25, 0.35, 0.5, 0.75])
        second_cover, second_miss = greedy_cover(period, remaining, alpha=alpha_second, rng=rng)
        if second_cover is not None:
            return (first_cover, second_cover), (0.0, 0.0)

        best_miss = min(best_miss, (0.0, second_miss))

    return None, best_miss


def lift_pair_to_original(pair: tuple[Cover, Cover]) -> tuple[Cover, Cover]:
    even_half, odd_half = pair
    even_classes = tuple(sorted((2 * modulus, 2 * residue) for modulus, residue in even_half.classes))
    odd_classes = tuple(sorted((2 * modulus, 2 * residue + 1) for modulus, residue in odd_half.classes))
    return (
        Cover(period=2 * even_half.period, classes=even_classes),
        Cover(period=2 * odd_half.period, classes=odd_classes),
    )


def print_density_report(candidate_moduli: list[int]) -> None:
    print(f"Candidate half-moduli ({len(candidate_moduli)}): {candidate_moduli}")
    print(f"Reciprocal sum on half side: {reciprocal_sum(candidate_moduli):.6f}")
    print(f"Reciprocal sum on original side: {0.5 * reciprocal_sum(candidate_moduli):.6f}")
    print(
        "Necessary mass for one half-cover: 1.000000 "
        f"({'passes' if reciprocal_sum(candidate_moduli) >= 1.0 else 'fails'})"
    )
    print(
        "Necessary mass for two disjoint half-covers: 2.000000 "
        f"({'passes' if reciprocal_sum(candidate_moduli) >= 2.0 else 'fails'})"
    )


def print_prime_power_screen(period: int, candidate_moduli: list[int]) -> None:
    print("Prime-power divisibility counts inside the candidate family:")
    for prime, exponent in prime_factors(period):
        for power in range(1, exponent + 1):
            modulus = prime**power
            count = sum(1 for value in candidate_moduli if value % modulus == 0)
            verdict = "enough for one side" if count >= prime else "too thin for one side"
            print(f"  divisible by {modulus:>4}: {count:>2} candidates, {verdict}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--period",
        default="2^3*3^2*5*7",
        help="Period on the half-modulus side. Example: 2^3*3^2*5*7",
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=200,
        help="Randomized greedy attempts per search",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=273,
        help="Random seed",
    )
    parser.add_argument(
        "--mode",
        choices=["report", "single", "pair"],
        default="pair",
        help="What to search for on the half-modulus side",
    )
    args = parser.parse_args()

    period = parse_factorization(args.period) if not args.period.isdigit() else int(args.period)
    candidate_moduli = half_moduli_dividing(period)

    print(f"Half-modulus period: {period}")
    print(f"Original period after lifting: {2 * period}")
    print_density_report(candidate_moduli)
    print_prime_power_screen(period, candidate_moduli)

    if args.mode == "report":
        return

    if args.mode == "single":
        if reciprocal_sum(candidate_moduli) < 1.0:
            print("Necessary reciprocal mass for one half-cover fails, so the search stops here.")
            return
        cover, miss = search_cover(period, candidate_moduli, trials=args.trials, seed=args.seed)
        if cover is None:
            print(f"No half-cover found. Best uncovered fraction: {miss:.6f}")
            return
        print("Half-cover found:")
        print(f"  {cover.describe()}")
        print(f"Verified uncovered fraction: {uncovered_fraction(period, cover.classes):.6f}")
        print("Lifted original congruences (one parity only):")
        lifted = Cover(
            period=2 * period,
            classes=tuple(sorted((2 * modulus, 2 * residue) for modulus, residue in cover.classes)),
        )
        print(f"  {lifted.describe()}")
        return

    if reciprocal_sum(candidate_moduli) < 2.0:
        print("Necessary reciprocal mass for two disjoint half-covers fails, so the search stops here.")
        return

    pair, miss = search_disjoint_pair(period, candidate_moduli, trials=args.trials, seed=args.seed)
    if pair is None:
        print(
            "No disjoint pair found. "
            f"Best misses were {miss[0]:.6f} on the first side and {miss[1]:.6f} on the second."
        )
        return

    even_half, odd_half = pair
    lifted_even, lifted_odd = lift_pair_to_original(pair)
    print("Disjoint half-covers found:")
    print(f"  even side: {even_half.describe()}")
    print(f"  odd side:  {odd_half.describe()}")
    print("Lifted original cover:")
    print(f"  even classes: {lifted_even.describe()}")
    print(f"  odd classes:  {lifted_odd.describe()}")
    all_classes = lifted_even.classes + lifted_odd.classes
    print(f"Verified on original period: {verify_cover(2 * period, all_classes)}")


if __name__ == "__main__":
    main()
