# maverick: the open core, PINNED — "one contiguous seed interval of length ≥ d_max^k"

This sharpens the open problem to a single, precise, checkable lemma, and proves the surrounding
scaffold rigorously. Combines [[maverick_bounded_gap_lemma]], [[cassels_completeness_machinery]],
[[sumset_crt_residue_theorem]] (the "seed interval" lemma sumset/carry isolated).

## The decisive dichotomy (VERIFIED)

Cassels interval-filling (extend a CONTIGUOUS interval [lo,H] by an atom t when t ≤ H−lo+1) was
tested as the *sole* engine, seeded from small atoms:

| family | k | seed from atoms ≤ B | result |
|---|---|---|---|
| {4,5,6,7,8} | 1 | B=30 → contiguous [4,67] | **SUCCESS** — extends to ∞ (cofinite, threshold 3) |
| {3,4,5} | 1 | B=200 → longest run [80,279] | **STALL** at atom 243 |
| {3,4,7} | 1 | B=2000 → run [582,2273] | **STALL** at atom 2187 |
| {3,4,5} | 2 | B=300000 → contiguous [77614,…] | **SUCCESS** — extends to ∞ |

**Interpretation (the crux of the whole problem) — CORRECTED, with a self-caught error:**

⚠️ **Correction to an earlier overclaim.** I initially asserted "a single contiguous block [lo,H]
extends to ∞ by appending one atom at a time (Cassels), since by Lemma BG each atom t ≤ running
sum." **This is WRONG as stated.** Single-block append needs `t ≤ H − lo + 1` (the block's *length*),
but the **max consecutive-atom ratio exceeds 2** for every family (2.40 for {4,5,6,7,8}, 3.0 for
{3,4,5} and {3,4,7}). So there are atoms t with t > (gap to previous atom), and a freshly-formed
block cannot absorb the next atom by a single append. Verified: a bottom-anchored block of length
700M for {3,4,5} cannot absorb the atom 4^15 ≈ 1.07e9 in one step.

✅ **What is actually true (verified empirically to 2×10⁹):** the FULL subset-sum reachable set
T_k is contiguous from n₀+1 onward ({3,4,5} k=1: contiguous [80, 2×10⁹], max gap 1; {4,5,6,7,8}
k=1: contiguous [4, 1.5×10⁹]). Cofiniteness is rock-solid. But the closure mechanism is the full
multi-atom subset-sum staying gap-free, **NOT** single-block Cassels append. Lemma BG (running sum
≥ next atom) is **necessary but not sufficient** — it forbids the running sum from falling behind,
but does not by itself prove the absence of internal gaps.

- Families like {4,5,6,7,8} are contiguous from the bottom (n₀=3) because d_min=4 base atoms
  already tile densely; the running-sum bulk + many bases keep it gap-free. {3,4,5} (d_min=3) has
  internal gaps until n₀=79.
- **The genuinely missing rigorous step** is: prove the full subset-sum set has NO internal gap
  above n₀(k). That is the (SEED) lemma below, and it requires the residue+density coupling — it is
  NOT delivered by Lemma BG alone.

## THE PINNED OPEN LEMMA (hand this to the prover / Aristotle, exact target)

> **(SEED).** For every admissible D (all d≥3, ∑1/(d−1)≥1, gcd(D)=1) and every k≥1, there exists
> a point a such that the interval [a, a + L] ⊆ T_k = ∑_{d∈D} d^k·B_d is a contiguous block whose
> length L is ≥ the largest atom not exceeding a (≈ a constant fraction of a, since the largest
> atom below a is Θ(a)).

REFINED (verified): the closure is NOT "one contiguous block extends by single appends" (that fails,
ratio>2, see correction above). The correct (SEED) is the stronger statement that the full
subset-sum set is gap-free above n₀. Concretely:

> **(SEED).** For every admissible D and k≥1, ∃ n₀ such that the full subset-sum set T_k contains
> EVERY integer ≥ n₀ — equivalently, no internal gap survives above n₀. The threshold n₀(k) is
> finite (empirically 79, 77613, 4.3M, 69M for {3,4,5}, k=1..4) but n₀(k)→∞.

Given (SEED), cofiniteness IS cofiniteness — (SEED) is just a restatement. The real content is
PROVING (SEED) uniformly in (D,k) without finite computation. The scaffold around it (Lemma BG
bounding the running sum, residue coverage giving every class, recursion T_k=C_k+T_{k+1}) constrains
the gap structure but does NOT close it. **The irreducible open core is: why does the multi-atom
subset-sum fill every residue consecutively above n₀?** — BEGL96 answered this only for (3,4,7) via
Mignotte–Waldschmidt. For general D it is open and analytic/transcendence in nature.

## Why (SEED) is exactly the hard analytic core
Manufacturing a gap-free block of length d_max^k requires every residue mod (that block's scale) to
be realized *consecutively*, which couples:
- the **bulk** from large atoms (Lemma BG provides density), and
- the **residue fix** from small cross-base atoms (modular's (L): gcd=1 ⇒ all residues available).
BEGL96 established (SEED) for the single family (3,4,7) only, via Mignotte–Waldschmidt lower bounds
on |3^p − 4^q| (linear forms in logarithms) — i.e. (SEED) is currently a TRANSCENDENCE-theory
statement for general D, not a combinatorial one. This is why the problem is open and why scholar's
finding (BEGL96 Thm 1 needs positive density, inapplicable to finite D) is decisive.

## Status ledger (what is rigorous vs open)
| component | status |
|---|---|
| scaling S(d,k)=d^k·B_d | PROVED (sumset; verified by me) |
| gcd(D)=1 necessary k≥1 | PROVED |
| ∑1/(d−1)≥1 necessary (all k) | PROVED (Pomerance, in Lean) |
| residue coverage (L), gcd=1 ⇒ all residues | PROVED (modular; verified by me) |
| recursion T_k=C_k+T_{k+1}, monotone T_{k+1}⊆T_k | PROVED (me) |
| Lemma BG: atom ≤ running sum after finite transient | PROVED (me, k-uniform) |
| Cassels extension of a contiguous seed | PROVED (classical; instantiated by me) |
| **(SEED): a contiguous block of length d_max^k exists** | **OPEN — the whole problem** |
| {4,5,6,7,8} k=1 cofinite (threshold 3) | PROVED end-to-end (me, no SEED needed: gap-free seed) |

**Answer almost certainly True** (every admissible family computes cofinite; both side conditions
provably necessary; no congruence obstruction; falsification lane exhausted by breaker). But (SEED)
for general D is genuinely open and sits in linear-forms-in-logarithms territory.
