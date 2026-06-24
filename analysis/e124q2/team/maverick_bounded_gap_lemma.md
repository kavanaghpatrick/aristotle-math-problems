# maverick: ⚠️⚠️ AUTHORITATIVE CORRECTION (supersedes everything below)

**FINAL STATUS (settled with cassels, exact computation): the MERGED Cassels predecessor-sum
condition `a ≤ S(<a)+1` HOLDS at every large atom, including every d_max^J.** Verified for (3,4,7)
k=1: S_merged(<7^J)/7^J ∈ [1.25, 2.38] for all J≥1 — never below 1, only the trivial a=3 start fails.

**BOTH framings below are WRONG by the SAME single-ray/truncation artifact:**
- The original "Lemma BG" (∑atoms<a / a ≥ 1) — its CONCLUSION (merged sum ≥ a) is actually CORRECT;
  my "it's FALSE" retraction was based on a truncated atom list AND on confusing the single-d_max-ray
  sum with the merged sum.
- The "inf Q1(a)/a = 1/(d_max−1), Cassels fails at every d_max^J" claim below — this is the
  SINGLE-d_max-RAY sum (only powers of d_max < a), NOT the merged Cassels predecessor sum. The merged
  sum is ~2a. So "Cassels fails at d_max^J" is WRONG; it HOLDS. (cassels caught this; I verified.)

**What is actually TRUE (use this):** the merged Cassels gap-condition holds for all large atoms
(σ>0 gives cassels' explicit onset m₀=(C'−1)/σ; even at σ=0 boundary it holds empirically with margin
≥1.25). So the obstruction is NOT "Cassels fails at scale" — it is PURELY the SEED / low-gap-closing
(the finitely many gaps below n₀ need residue coverage, not running-sum). My genuine surviving point
(Result 2): gap-condition-holds ≠ cofinite, because the low gaps below n₀ are real and need the
residue+density argument. THAT stands. The "1/(d_max−1)" and "Lemma-BG-is-false" claims do NOT.

---

## [SUPERSEDED — single-ray artifacts, retained for the record only] earlier text follows:

**STATUS: my earlier "Lemma BG" was FALSE. This file documents the retraction and the correct,
sharper finding it led to. The correct finding is more valuable than the wrong lemma.**

## What I claimed (WRONG)
"Lemma BG: if ∑1/(d−1)≥1, then sorting atoms ascending, t_{n+1} ≤ T_n (running sum) after a finite
transient; proof: (∑atoms<a)/a → ∑1/(d−1) ≥ 1." I sent this to cassels and carry as rigorous.

## Why it is FALSE (verified)
The ratio `Q1(a)/a := (∑ atoms of value < a)/a` does **NOT** converge to ∑1/(d−1) and does **NOT**
stay ≥ 1. My original computation only sampled atoms ≤ 10¹², where the ratio happened to be 1.16.
Over the full range (atoms up to 10¹⁵⁰) the ratio **OSCILLATES** and its **infimum is exactly
1/(d_max − 1)** (= 0.25 for {3,4,5}, d_max=5), attained **exactly at powers of the largest base**:

| family | inf Q1(a)/a | where |
|---|---|---|
| {3,4,5} | 0.2500 = 1/(5−1) | a = 5^J (verified at J=185,186,187) |

So the classic single-pass **Cassels condition `t_{n+1} ≤ T_n + 1` FAILS** — by a factor of ~4 —
at every large power of d_max. (Verified: 17 of 169 atoms violate it for {3,4,5}.) **The running
sum is 4× too small right at powers of d_max.**

## The CORRECT picture (this is the real, sharper result)

**Cofiniteness here is NOT a Cassels/Birch single-pass completeness phenomenon.** When the running
sum falls behind at a = d_max^J, a gap-region opens; it is closed only by **multi-atom subset sums**
that REUSE the large atom a itself together with smaller atoms of the other bases. The infimum
1/(d_max−1) is the exact quantitative reason single-block / single-pass arguments cannot work, and
it is the same wall that forced BEGL96 to use Mignotte–Waldschmidt linear-forms-in-logs for (3,4,7)
rather than a Cassels argument.

### Why it matters for the proof obligation
- The reachable set IS cofinite (verified to 2×10⁹ for {3,4,5} k=1 and {4,5,6,7,8} k=1, max gap 1).
- But NO running-sum-dominance lemma proves it. The proof must control how the multi-atom subset
  sums fill the [d_max^J, next] regions — exactly the residue-coverage-in-every-window statement
  (the (SEED) lemma), and it is genuinely analytic/transcendence-flavored.

### What survives from the wrong lemma
The asymptotic AVERAGE reciprocal mass still equals ∑1/(d−1) (correct on average / in Cesàro sense);
the harmonic condition is still the right invariant. What is FALSE is the pointwise claim that the
running sum dominates the *next* atom — it does not, at powers of d_max.

## Corrections sent
Retraction messaged to cassels and carry (who received the wrong lemma). The honest reduction to
(SEED) in [[maverick_seed_interval_pinned]] stands and is UNAFFECTED — (SEED) was always stated as
"full subset-sum gap-free above n₀," which is correct; it never depended on the false BG.

## Net
The infimum-1/(d_max−1) finding is the genuine contribution: it PROVES that this problem cannot be
closed by any Cassels/Birch-style running-sum argument, pinpointing exactly why it is open and why
BEGL96 needed transcendence theory. A correct sharp negative result replacing a wrong positive one.
