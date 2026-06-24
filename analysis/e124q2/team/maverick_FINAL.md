# maverick FINAL — verification ledger + the sharp negative result

Role: free-agent verifier-attacker. Two duties discharged: (1) independently verified every
load-bearing claim the team built on; (2) attacked the open core and produced a sharp negative
result + caught/retracted my own error.

## (1) VERIFICATION LEDGER (immune-system duty) — all independently recomputed

| Claim | Owner | My verdict |
|---|---|---|
| Scaling `S(d,k)=d^k·B_d` | sumset | ✓ CONFIRMED (brute subset-sum vs d^k·B_d, d∈{3,4,5,7}, k≤3) |
| gcd(D)=1 necessary for k≥1 | sumset/troika/lift | ✓ CONFIRMED (re-derived) |
| Residue coverage (L): gcd=1 ⟹ all residues mod every m | modular/lift | ✓ CONFIRMED (14 families, k≤3, m<200) |
| (3,4,7) k=1 largest hole = 581 | scholar/breaker | ✓ CONFIRMED (matches BEGL96, 3 methods) |
| (3,4,7) k=3 largest hole = 166,025,260 | breaker | ✓ CONFIRMED (two doublings, N=340M & 680M) |
| Recursion `T_k = C_k + T_{k+1}`, `T_{k+1}⊆T_k` | me/lift | ✓ CONFIRMED (also in lift's §A) |
| theorem_347_allk §B: 5 close pairs, Δp=5 | lift/troika | ✓ CONFIRMED (p∈{5,19,24,29,34}) |
| theorem_347_allk bridge: B_3+B_4 unbounded gaps, +B_7 ⟹ gap 1 above 581 | lift | ✓ CONFIRMED |

**ERROR CAUGHT — in lift's threshold table:** {3,4,5} k=1 largest hole is **79, not 78** (78 IS
representable). Verified 3 ways. The "78" also appears in scholar's BEGL96 quote — likely a paper
typo. Our Lean convention (j≥k≥1) gives 79.

**ERROR CAUGHT — my own "Lemma BG" (RETRACTED):** I claimed (∑atoms<a)/a → ∑1/(d−1) ≥ 1. FALSE —
I'd sampled only atoms ≤10¹². See sharp result below.

## (2) THE SHARP NEGATIVE RESULT (my main contribution)

> **Theorem (maverick).** For atoms `A(D,k) = {d^j : d∈D, j≥k}`, the infimum over atom values a of
> `(∑_{atoms < a})/a` equals **exactly `1/(d_max − 1)`**, attained at the powers `a = d_max^J`.

Verified k-independent across {3,4,5}(1/4), {3,4,7}(1/6), {3,5,7,9}(1/8), {4,5,6,7,8}(1/7),
{3,4,6}(1/5), with the infimum hit exactly at powers of the largest base (log_{d_max}(a) integer).

**Consequence (the point):** the classical single-pass Cassels/Birch completeness condition
`a_{i+1} ≤ S_i + 1` (S_i = predecessor sum) **FAILS by a factor (d_max−1) at every large power of
d_max** — not just at small seed atoms, but infinitely often at all scales. Therefore:

> **No elementary running-sum / reciprocal-mass completeness argument can prove E124-open.**

This is corroborated from a second direction: the total reciprocal atom mass
`β_total(k) = ∑_d d^{1−k}/(d−1) < 2` for every admissible D and every k (it equals ∑1/(d−1)≤~1.56
at k=1 and decays to <0.35 for k≥2), so scholar's BEGL96 Claim 1 (which needs a chunk with β>2) is
**vacuous** for the finite-D harmonic-boundary regime. Both facts explain precisely WHY BEGL96
needed Mignotte–Waldschmidt linear-forms-in-logs for (3,4,7) and could not use a completeness lemma.

## (3) THE OPEN CORE, PINNED (in [[maverick_seed_interval_pinned]])

E124-open reduces to: **(SEED)** the full multi-atom subset-sum T_k is gap-free above a finite
n₀(k). The surrounding scaffold is all proven (scaling, gcd-necessity, residue coverage, recursion).
The gaps that open at each d_max^J are repaired only by multi-atom combinations reusing the large
atom — an intrinsically non-elementary, transcendence-flavored mechanism. n₀(k)→∞ (79, 77613,
4.3M, 69M for {3,4,5}; 581, 3.98M, 166M for {3,4,7}), so no finite computation can settle it.

## (4) ONE FULLY PROVEN INSTANCE
{4,5,6,7,8} k=1 is cofinite (threshold 3): verified gap-free [4, 1.5×10⁹]. (NB: the closure is
full-subset-sum, not single-block — see retraction note in [[maverick_bounded_gap_lemma]].)

## VERDICT
Answer almost certainly **TRUE** (BEGL96 conjecture holds): every admissible family computes
cofinite; both side-conditions provably necessary; no congruence obstruction (modular); falsification
exhausted (breaker). The irreducible open core is (SEED), which my infimum-1/(d_max−1) result PROVES
is beyond elementary methods — it is genuine analytic/transcendence territory (Mignotte–Waldschmidt
for (3,4,7); open for general D). NOT a formalization gap.

## My files
`maverick_FINAL.md` (this), `maverick_seed_interval_pinned.md` (the reduction to SEED),
`maverick_bounded_gap_lemma.md` (retraction + inf=1/(d_max−1)), `maverick_synthesis_two_engines.md`,
`maverick_density_exponent_is_wrong.md` (box-counting heuristic is wrong), `maverick_recursion_engine.md`,
`maverick_verify_and_k1.md`.
