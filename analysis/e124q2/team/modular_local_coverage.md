# E124 open part: the LOCAL (congruence) theory — complete characterization

**Author:** modular. **Status:** Central lemma EMPIRICALLY CONFIRMED (m<200, many D, k∈{1,2,3}),
proof of effective bound IN PROGRESS. Core computations verified against brute force.

Builds on [[sumset_reduction_scaling]] (sumset): the open problem is whether
`∑_{d∈D} d^k·B_d` is cofinite, where `B_d = S(d,0)` = base-d 0/1-digit numbers.

---

## Setup and verified computational core

`B_d mod m` = subset-sum closure of the residues `{d^j mod m : j ≥ 0}`, where a residue that
recurs **infinitely** (in the eventual cycle) is available with **unbounded multiplicity**, while a
residue appearing only in the **pre-period** is usable **at most once**. Code: `/tmp/local_core.py`,
function `Bd_mod(d,m)`. Verified against brute-force enumeration of B_d (200 random (d,m) for B_d,
150 for the k≥1 scaled version `Sdk_mod`): **ALL PASS**.

`S(d,k) mod m = { (d^k·r) mod m : r ∈ B_d mod m }` (modular multiplication is exact here).

---

## THEOREM A (coprime ⇒ full). If gcd(d,m)=1 then B_d mod m = ℤ/m (full).

**Proof.** If gcd(d,m)=1 then d is a unit mod m, so j ↦ d^j mod m is **purely periodic** (no
pre-period) and returns to d^0 = 1. Hence 1 lies in the cycle ⇒ available with unbounded
multiplicity ⇒ the achievable set contains {0,1,2,…} mod m = all of ℤ/m. ∎
Confirmed: no counterexample for all d∈[3,30), m∈[2,80), gcd=1.

**Corollary.** The local obstruction for a single B_d lives **only** at primes p | gcd(d,m).

## THEOREM C (single prime power, p | d). For p | d, write v = v_p(d) ≥ 1 and j* = ⌈a/v⌉.

`B_d mod p^a` = subset sums of `{d^0, d^1, …, d^{j*-1} mod p^a}`, each used at most once; it has
exactly `2^{j*}` residues. (Because d^j ≡ 0 mod p^a for all j ≥ j*, so only the first j* powers
matter, and they are linearly independent enough that the 2^{j*} subset sums are distinct.)
This is a Cantor-like "low-digits" set: the residues whose base-d expansion uses only digits 0/1
in positions < j*. Confirmed for many (d,p,a).

## THEOREM B′ (CRT — corrected; the SUBTLE point).

`B_d mod m` is **NOT** the CRT product `∏_p (B_d mod p^a)` in general (fails for d=6,10,12,14 —
any d with ≥2 distinct prime factors). Reason: the digit pattern (which powers d^j to include) is
**shared** across all prime components — the same Finset s must be used simultaneously. So
`B_d mod m` is the CRT image of the **diagonal** subset-sum set of the vector sequence
`(d^j mod p_1^{a_1}, …, d^j mod p_r^{a_r})`, a generally **proper** subset of the product.
This coupling within a single d is real but only bites when d is composite with several primes.

---

## CENTRAL LOCAL LEMMA (the one every proof strategy on this team needs)

> **(L)** If gcd(D) = 1 then for every k ≥ 1 and every modulus m,
> `∑_{d∈D} d^k·B_d  ≡  ℤ/m` (covers all residues).

**Status: EMPIRICALLY CONFIRMED.** Tested all m < 200, k ∈ {1,2,3}, on ~20 admissible D
including (3,4,7), (3,4), (3,5), (4,5), (3,4,5), (6,10,15), (4,6,9), (3,4,9), (6,9,10), (4,9,49),
(3,8,9), (5,6,7), (2,3), etc. **Zero coverage failures whenever gcd(D)=1.**

**Sharp converse (the obstruction):** if gcd(D) = g > 1, pick prime p | g. Every element of every
d^k·B_d is divisible by p (since p|d, k≥1), so the whole sumset ⊆ pℤ — **misses every m with p|m**.
Confirmed: D=(4,6,10), gcd=2, misses all even m. **This is the unique local obstruction at k≥1.**

**Note on ∑1/(d−1)≥1:** this condition is NOT needed for local coverage — it is a *density/size*
constraint (Pomerance converse), orthogonal to residue coverage. The two side-conditions of BEGL96
are genuinely independent: **gcd(D)=1 governs LOCAL (residue) solvability; ∑1/(d−1)≥1 governs
GLOBAL DENSITY.** (Q) asks whether together they suffice — local coverage alone does not, because
of the *size-control / carry-debt* issue (see §"bounded carry debt" below, in progress).

---

## Proof of (L) — MACHINE-PROVED (Aristotle, Jun 10 2026); canonical argument is the SUBGROUP one

**The proof is now formalized in Lean (sorry-free, standard axioms):**
`submissions/results_jun10/residue_coverage_x/…/RequestProject/Main.lean`, theorem
`erdos124_residue_coverage`. The canonical argument is NOT the CRT-recombination I first sketched
(that was FLAWED — see below) but a clean **subgroup** argument:

1. The sumset's achievable-residue set H = ∑_{d∈D} (d^k·B_d mod m) is a submonoid of (ℤ/m,+); a
   submonoid of a finite group is a **subgroup** ⟹ H ≤ ℤ/m is a subgroup of a cyclic group.
2. gcd(D)=1 ⟹ for each prime p|m there is d_p∈D with p∤d_p, and d_p^k mod m ∈ H is **not divisible
   by p** (a per-prime witness).
3. A subgroup of cyclic ℤ/m is dℤ/m for some d|m; if d>1 a prime p|d divides every element,
   contradicting the Step-2 witness. So d=1 and **H = ℤ/m**. ∎

**RETRACTION of my original sketch:** I had proposed combining the per-prime full-coverages "via CRT,
the patterns being independent across distinct bases d." Aristotle showed this is FLAWED: a single
base d contributes ONE number mod m, which generally leaks into all CRT blocks — you cannot force
d_p's pattern to hit its assigned block and vanish elsewhere. The global subgroup argument above is
the correct replacement and needs no per-block CRT bookkeeping. (The CONCLUSION was always correct —
triple-verified empirically — only my intermediate argument was wrong.) **Also: the d≥3 and D-nonempty
hypotheses are UNNECESSARY** — (L) holds for arbitrary finite D and any k≠0 (Aristotle generalization).

---

## Files
- `/tmp/local_core.py` — verified Bd_mod / Sdk_mod / sumset_mod
- `/tmp/local_structure.py`, `/tmp/local_coprime.py`, `/tmp/local_correlate.py`, `/tmp/sumset_coverage.py`
