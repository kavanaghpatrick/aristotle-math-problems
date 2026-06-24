# sumset — SUMMARY of contributions to E124 open part (BEGL96 conjecture)

**Problem:** for k≥1 and admissible D (all d≥3, ∑1/(d−1)≥1, gcd(D)=1), is `∑_{d∈D} S(d,k)` cofinite?
**Predicted answer (team consensus + my data):** TRUE, but the proof needs Baker-type input (open).

## My rigorous, verified results (Lean-ready where marked)

1. **Scaling reduction** [PROVED, 1 line] — `S(d,k) = d^k·B_d`, B_d = 0/1-digit base-d numbers.
   So the sumset is `T_k(D) = ∑_{d∈D} d^k·B_d`. (sumset_reduction_scaling.md)

2. **gcd necessity** [PROVED] — if prime p | gcd(D) then p^k divides every element of T_k, so T_k
   ⊆ p^k·ℕ is not cofinite. gcd(D)=1 is NECESSARY for k≥1 (and automatic at k=0 since d^0=1). This is
   the structural reason BEGL96 adds gcd=1 only for k≥1. (sumset_reduction_scaling.md)

3. **Theorem B — residue coverage** [PROVED] — for every modulus M,
   `T_k(D) mod M = gcd(gcd_{d∈D}(d^k), M)·(ℤ/M)`. Hence T_k meets EVERY residue class mod EVERY M
   ⟺ gcd(D)=1. This fully resolves the CONGRUENTIAL obstruction: with gcd=1 there is no modular
   barrier at any scale, so any failure of cofiniteness must be archimedean (a skipped interval),
   never a missed arithmetic progression. (sumset_crt_residue_theorem.md)

4. **Theorem C — deconvolution identity** [PROVED] — `∑_{d∈D} B_d = L_k(D) + T_k(D)` where
   L_k = ∑_{d∈D}(B_d ∩ [0,d^k)) is a FIXED finite set. So the OPEN k≥1 sumset is the SOLVED k=0
   sumset minus a finite Minkowski deconvolution. Localizes the open content to: "does dividing out
   a fixed finite set from a cofinite set preserve cofiniteness, given no residue obstruction?"
   (sumset_deconvolution_reduction.md)

## My honest negative results (saved the team from dead ends)

5. **Theorem B + Theorem C are NOT sufficient** [explicit counterexample] — `L+T cofinite` + `T hits
   all residues` does NOT imply `T cofinite` (counterexample: L={0,1,2,3}, T=ℕ∖{powers of 10}). The
   soft/structural route cannot close the problem; the archimedean (SEED) lemma is genuinely needed.
   This independently confirms maverick's Result 2 and cassels §4. (sumset_deconvolution_reduction.md)

6. **Sieving cannot prove cofiniteness — distant-gap trap** [demonstrated] — "no gaps up to N" is NOT
   evidence of cofiniteness. (4,5,6) looks cofinite to 7.8M (1 gap by 20M) but has 2.4M gaps by 60M.
   I got caught by this myself: my early (3,4,7) k=2 threshold of 785,743 was a truncation artifact;
   the true value is 3,982,888 (cassels/breaker, re-verified). The folklore bound density(S) ≤
   ∑1/(d−1) is also FALSE as stated (measured (3,4) density 0.884 > 5/6). Warned the whole team:
   trust GAP-FINDING, never coverage. (sumset_converse_anomaly.md, sumset_empirical_landscape.md)

7. **Threshold growth law** [empirical] — strict excess ∑>1: threshold(D,k) = Θ((d_max·d_2nd)^k),
   decreasing in the harmonic excess. Boundary ∑=1: threshold ≫, Baker-type, irregular — THE hard
   frontier. Tells you how far to compute and confirms the ∑>1 vs ∑=1 split.

## Where this lands (consistent with cassels/maverick/scholar/breaker)

E124-open reduces to a single archimedean lemma. Combining my Theorem B (residue coverage from
gcd=1) with maverick's Lemma BG (bounded gaps from ∑1/(d−1)≥1) and cassels' Lemma C (step-M Cassels
filling), the entire open content is the sharp obligation:
> **(★)** for n ≥ n₀(D,k), every residue mod G(k) is realized within every O(G(k))-window.
This is linear-forms-in-logarithms / Mignotte–Waldschmidt territory; BEGL96 settled it ONLY for the
single triple (3,4,7) at the boundary. The strict-excess regime ∑>1 is the more tractable target
(maverick's ladder + my clean threshold law), and is where a general proof is most likely to land.

## Reproduce
Scripts in analysis/e124q2/team/code/: cofin_check.py (python-int bitset), big_check.py (numpy
sieve), density_decay.py (windowed gap density). All cross-validated against BEGL96's (3,4,7) k=1
value 581 and the corrected k=2 value 3,982,888.
