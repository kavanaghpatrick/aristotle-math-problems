# Strategic Context: Math Project — May 29 2026

## Mission

Submit bare-gap conjectures to Aristotle. We do NOT write proof strategies. Aristotle finds the path. Hard rules: INFORMAL .txt sketches ≤30 lines, no proof guidance, auto-attach prior Aristotle results as context.

## Aggregate Stats (1165 submissions total)

| Status | Count | Notes |
|---|---|---|
| compiled_no_advance | 742 | Main failure mode — clean Lean, no advance |
| compile_failed | 262 | Lean build failed |
| compiled_partial | 107 | Sorries remain |
| submitted | 38 | Inflight or pre-rubric |
| disproven | 14 | Counterexample / falsification |
| **compiled_advance** | **2** | **Genuine gap resolutions (strict rubric)** |

Historical hit rate (compiled_advance): 2/1165 = **0.17%**.

## The Two Advances (both this week)

### slot720 — Feit-Thompson p=3, q≡71 mod 72
- **Structural proof iter1→iter2** pattern.
- iter1: single (3,71) pair via manual lemmas.
- iter2: generalized to all primes q ≡ 71 (mod 72) with q ≤ 1000 ({71,359,431,503,647,719,863}) via Fermat little theorem reducing 3^q mod p before computation.
- Used Wieferich context (slots 612/613). Aristotle picked small prime divisors p | A(q) per q.
- Does NOT resolve full FT prime conjecture. Real structural advance.

### slot722 — Brocard, n ∈ [2,500]
- **Same iter1→iter2 pattern.**
- iter1: 50 manual have-lemmas (would explode at scale).
- iter2: custom computable `nthPrimeComp` function bridged to `Nat.nth Nat.Prime` via `Nat.nth_count`. Parametrized by N.
- `native_decide` for bulk per-n verification but framing is structural.
- Closes small-n gap toward Ferreira (2023) asymptotic. Does NOT resolve Brocard.

**Common DNA of both advances:** custom computable bridge function + Fermat/native_decide reduction + iter2 generalizes over a parametric residue class or range.

## Active Near-Misses (1 sorry remaining)

### slot724 — Erdős 203 (2D covering)
- Conjecture: ∃ m coprime to 6 such that 2^k·3^l·m+1 is composite for all k,l≥0.
- Aristotle proved sorry-free `index2_covering_insufficient` in side file `Covering.lean`: the 11 index-2 primes below 300 (where ⟨2,3⟩ has index 2 in (ℤ/pℤ)*) cannot cover. Union bound: max-coverage 10+6+4+4+3+2+2+2+2+2+2 = 39 < 100 cells in 10×10 grid.
- Main theorem still `sorry`. Aristotle: "the original problem remains an open problem in mathematics."
- Honest limitation: density sum ∑ 2/(p-1) over index-2 primes **diverges** by Dirichlet, so the density argument doesn't rule out covering with sufficiently many index-2 primes. Index-1 primes (almost all) cover only 1/(p-1) but are vastly more numerous.

### slot723 — Erdős 647 (divisor gaps)
- Conjecture: ∃ n > 24, max_{m<n} (m + τ(m)) ≤ n + 2.
- Aristotle: **conjecture as posed is FALSE**.
- Sorry-free `native_decide` verifies failure for n ∈ [25, 2999].
- Sorry-free witness lemmas for n ≥ 3000: odd n, even n with 3∣(n−2), even n with 3∣(n−1), even n≡0 mod 6 with n−1 composite, n−1 prime but τ(n−2)≥5.
- **1 sorry** in `witness_for_all`: case n ≡ 0 (mod 6), n ≥ 3000, n−1 prime, (n−2)/2 prime (Sophie Germain pair). Needs (4·((q−1)/2)+1)/3 composite for q ≥ 1499. Computationally verified to n ≤ 10^6 but general proof would require covering systems or sieve methods on Cunningham chains — itself an open problem.

## Recent Activity (last 14 days)

| Slot | Task | Status | Sorry |
|---|---|---|---|
| 717 | Erdős 850 bare | compiled_no_advance | 0 |
| 718 | Erdős 850 claude sketch | compiled_no_advance | 0 |
| 719 | Erdős 850 bare then ask | compiled_no_advance | 0 |
| 720 | FT p=3 q≡71 mod 72 | **compiled_advance** | 0 |
| 721 | Leinster nonabelian S3×C5 | FAILED | — |
| 722 | Brocard n∈[2,500] | **compiled_advance** | 0 |
| 723 | Erdős 647 existence δ | NEAR_MISS | 1 |
| 724 | Erdős 203 covering | NEAR_MISS | 1 |

8 submissions → 2 advances = 25% hit rate, vs historical 0.17%. The iter1→iter2 framing appears in both advances.

## Problem Concentration (top by volume)

| problem_id | n | advances | disproven | near-miss |
|---|---|---|---|---|
| **tuza_nu4** | **317** | **0** | 4 | 83 |
| erdos_707 | 14 | 0 | 0 | 0 |
| feit_thompson | 12 | 1 | 0 | 0 |
| leinster | 10 | 0 | 0 | 1 |
| erdos850 | 10 | 0 | 1 | 0 |
| path4_tau_le_8 | 9 | 0 | 0 | 1 |
| erdos_647 | 9 | 0 | 0 | 0 (now 1 with 723) |
| tuza_nu3 | 8 | 0 | 0 | 3 |

**Tuza nu=4 accounts for 27% of all submissions and produced ZERO advances despite 4 disproofs and 83 near-misses.**

## Falsified Approaches (from memory)

- Tuza: apex-based bridge coverage, 6-packing, LP duality, universal apex — all dead.
- FT p=3, q≡71 mod 72: Kummer symbol, Eisenstein reciprocity, all standard approaches exhausted (BEFORE slot720 advance via Fermat reduction + iter2 pattern).
- FT p=3, q≡8 mod 9: 9th power residue, CM curves, polynomial relations, LTE — all dead.

## User Directives (memory)

1. "We care about NOVEL solutions, not formalization."
2. "HAVE FAITH IN ARISTOTLE. DO NOT BE AFRAID OF FAILURE."
3. "Gap-targeting only — bare conjecture, zero guidance."
4. "Depth over breadth — focus 5 problems deeply, not 500 shallowly. 0.8% hit rate demands concentration."
5. NEVER state a gap as `(P) ∨ ¬ P` — Aristotle resolves with `exact em _`. State existence or impossibility separately.

## Debate Questions (the actual ask)

1. **iter1→iter2 pattern** — Is the slot720/722 structural-framing pattern reproducible? Should it be systematized as a default for all submissions, or are slot720/722 lucky exceptions? What is the actual mechanism — custom computable bridge functions, parametric scaling via Fermat reduction, both?

2. **slot723 Erdős 647 resub** — Push the Sophie Germain Cunningham-chain sub-case via iter2 framing on the residue class q ≡ 71 mod (something), or is the Cunningham chain compositeness reduction a true dead end (since it's itself an open sieve problem)?

3. **slot724 Erdős 203 resub** — Resub targeting the complementary **index-1 primes covering question** (the divergent-density attack Aristotle flagged), or pivot? Is there an iter2-shaped opening?

4. **Tuza nu=4 abandonment** — Formally abandon? It's 27% of historical volume with zero advances, all standard approaches falsified per memory. Or is there a structural reframing (apex-free, non-LP, non-6-packing) worth one final shot?

5. **The 5 problems for next month** — Given:
   - 2 active near-misses (E203, E647).
   - 2 successful structural advances (FT family, Brocard small-n) — both invite iter3 generalizations (larger residue classes, larger n).
   - Memory says concentrate on 5.
   - Hit rate is 25× higher in last 14 days than historical.
   Which 5? Defend the list against alternatives.
