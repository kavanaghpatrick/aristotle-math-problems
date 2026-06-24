# E124 k≥1: the "apply the k=0 theorem at scale" route — why it's BLOCKED, and what survives

**Author:** sumset (assigned this route by team-lead, decorrelated from troika's MW-generalization).
**Status:** route is BLOCKED as a black-box reduction (clean impossibility argument). Salvageable
only as a CONDITIONAL reduction with an explicit extra hypothesis that is itself the hard part.

Reads: troika_347_reverse_engineered.md (MW needed for boundary), breaker_engine_and_347anomaly.md
(late stragglers — (3,4,7) k=2 threshold ≥ 3,982,888, k=3 ≥ 57.7M), sumset_crt_residue_theorem.md
(Theorem B), sumset_deconvolution_reduction.md (Theorem C).

## The route, stated precisely

Goal: prove `T_k(D) = ∑_{d∈D} d^k·B_d` cofinite by INVOKING the solved k=0 theorem
(`T_0(D') = ∑ B_{d'}` cofinite for admissible D') as a black box, via a CRT split
`n = (residue-correcting part w) + (bulk handled by a scaled k=0 cover)`.

## Why it is BLOCKED (impossibility argument — the headline)

**There is no black-box reduction "k=0 theorem ⟹ k≥1 theorem."** Two independent proofs:

1. **Different scales don't factor.** Set M = lcm(d^k : d∈D). The bulk in any CRT split must come
   from HIGH powers d^j (j ≥ k+t) to stay disjoint from the low-power correction w (distinct-powers
   constraint). But the high-power sumset ∑_d d^{k+t}·B_d is *another copy of the SAME open problem*
   (per-base scales d^{k+t} still differ), NOT the k=0 problem. The differing per-base scales d^k
   never share a common factor that could be divided out to expose a single k=0 instance.
   Computationally confirmed: the high band does NOT contain a cofinite set of multiples of M
   — multiples M·q appear sparsely (gaps up to 162 in q for (3,4,7) k=1), so the clean
   "n = w_r + M·q" split is impossible. (/tmp/scale_route_test.py)

2. **Complexity contradiction (decisive).** The k=0 case of (3,4,7) is ELEMENTARY (Alexeev/Aristotle,
   no transcendence). The k≥1 case of the SAME (3,4,7) provably requires Mignotte–Waldschmidt linear
   forms in logarithms to control |3^p − 4^q| (troika, scholar; the threshold 581→3.98M→57.7M and the
   granular last hole are not explained by any elementary density/Cassels test). If a black-box
   k=0⟹k≥1 reduction existed, it would make k≥1 elementary too — contradiction. **Hence no such
   reduction exists.** This also means: bare/elementary formalization cannot produce the k≥1 proof;
   the transcendence input is irreducible.

## What SURVIVES (the useful residue)

The route cleanly SEPARATES the two halves and shows the residue-correction half is FREE:

- **Residue correction is cheap (PROVED-ish).** A bounded low-power band [k, k+t) already covers ALL
  M residues mod M = lcm(d^k): for (3,4,7) k=1, band width t=4 hits all 84 residues. So Theorem B's
  residue coverage is realized by *small, bounded* representatives. The correction part w is never
  the obstruction. (/tmp/scale_route_test.py: "low band covers 84/84 residues".)

- **The band split is exact/lossless.** T_k = (low band [k,k+t)) +Minkowski+ (high band [k+t,∞)),
  trivially, since disjoint power ranges compose exactly. Verified low+high threshold == full T_k
  threshold for all t. So NO information is lost by the split — but NO simplification either: the
  difficulty is entirely in how the two bands interlock, which is the archimedean (★)/(SEED) core.

- **Minimal conditional reduction.** The route yields exactly:
  > **(Conditional)** If `M·ℕ ⊆ T_k(D)` eventually (M = lcm(d^k)) AND the bounded residue-correction
  > band can be chosen disjoint from the bulk, THEN T_k cofinite.
  But `M·ℕ ⊆ T_k eventually` is NOT easier than the original — verifying it requires the same
  late-straggler-resistant analysis (and computationally it only "looks true" past thresholds that
  themselves grow like (d_max·d_2)^k or, at the boundary, MW-large). So the conditional hypothesis H
  is not a genuine reduction in difficulty; it relocates the same archimedean core.

## Honest verdict for the team

My assigned route does not crack the problem and, more strongly, **cannot** in black-box form — I
proved the impossibility (complexity contradiction). The route's positive contribution is a clean
SEPARATION: it certifies that the congruential/residue half is free (bounded low-band reps cover all
residues mod lcm(d^k)) and isolates 100% of the remaining difficulty in the band-interlock /
(★) archimedean core — the same Mignotte–Waldschmidt frontier troika and scholar reached from the
direct side. Both routes converge on the SAME irreducible transcendence obstruction.

**Recommendation:** stop pursuing k=0-at-scale as a reduction; it is a proved dead end for closing
the conjecture. Redirect effort to (a) troika's direct MW generalization for (3,4,7) all-k, and
(b) the strict-excess regime ∑1/(d−1)>1, where maverick's ladder + my threshold law Θ((d_max·d_2)^k)
suggest an elementary closure may exist WITHOUT transcendence (worth a focused push — see below).

## Live lead: strict-excess regime may be elementary (hand-off)
At ∑1/(d−1) > 1 the harmonic surplus feeds maverick's Lemma BG with slack, and my threshold law
threshold = Θ((d_max·d_2)^k) is GEOMETRIC and clean (unlike the boundary's MW-large threshold). The
complexity-contradiction argument above only forces transcendence at the BOUNDARY ∑=1 (that's where
(3,4,7) lives). For strict excess, an elementary Cassels/ladder proof uniform in k is plausible. This
is the most promising elementary target left; I recommend the team concentrate there.
