# carry — HANDOFF (constructive/algorithmic lane, E124 open part)

Full detail: `carry_constructive_findings.md`. This is the ≤1-page successor brief.

## (1) VERIFIED RESULTS (all by exhaustive bitset subset-sum DP / direct construction)

- **BEGL96 holds for all 45 admissible D (d≤12, r≤4): cofinite at k=1 AND k=2. No counterexample
  anywhere** (incl. larger/sparser stress D up to 9 bases). Disproof lane is dead for small D.
- **Reformulation:** E124-open ⟺ atom set A(D,k)={d^j:d∈D,j≥k} is a complete sequence (every large
  n a subset sum). Via sumset's S(d,k)=d^k·B_d.
- **gcd>1 obstruction (clean proof):** p|gcd(D) ⟹ p^k | every representable n ⟹ not cofinite.
- **+b^k closure / per-class structure (my Obs 1, → cassels' Lemma C):** each residue class mod
  M=b^k (b=min D) is a full AP above its per-class threshold; threshold T = (last +M-closure
  failure)+M. cassels proved Lemma C and the side-condition MAPPING: (a) M-consecutive-run ⟺ gcd=1;
  (b) +M-closure ⟺ ∑1/(d−1)≥1. I re-verified the mapping with controls.
- **Isolated-gap mechanism:** late missing values are ISOLATED singletons (264,521,581 for (3,4,7)k1)
  sitting where powers cluster (3^5=243≈4^4=256). This is the Mignotte–Waldschmidt regime.
- **Verified thresholds:** (3,4,7) k1=581, k2=**3,982,888** (NOT 785743 — see traps); (3,4,5) k1=79.

## (2) WORK IN FLIGHT / where I stopped

**task #17 (strict-excess theorem) — ASSAULT CONCLUDED, honest partial.** What we BANKED:
- **Per-(D,k) finite verifiability** (cassels + lift + modular + me): for each FIXED (D,k) at σ>0,
  cofiniteness is a FINITE computation (verify to threshold + bounded-gap/closure tail), machine-
  verifiable and verified for all small D. Ingredients: Lemma A (gap-onset m₀=(C'−1)/σ) + lift's
  Lemma B (margin r(n)→∞) + modular residue + my class-wise full-AP (each class mod b^k full AP at
  FINITE onset — verified (3,4,5) k=2 all 9 classes, k=3 all 27 classes). **PRECISION (carry+sumset):
  this is NOT a uniform-over-D elementary theorem even at fixed k — N₀(D,k) needs MW to bound a priori
  for clustered D, so it's case-by-case verification, not "all admissible D at this k" elementarily.**
- **Subset-monotonicity** (sumset): reduces non-minimal D (72/115 strict-excess D, d<12). The 43
  MINIMAL D (the {3,4}-clustering hard core) are NOT reduced.
- **Lemma A' (my class-onset bound):** N₀(D,1) ≤ 0.27·C'/σ² is FITTED, NOT clean — grazed/exceeded by
  (3,4,6) (ratio 0.2716>0.27; cassels/lift caught it). Even k=1 closure is VERIFIED-not-PROVEN (N₀
  finiteness = MW kernel). Genuinely-unconditional = only k=0 (known) + non-minimal D (subset-monotonicity).
- **Lemma PCA (my per-class-AP lemma, written into the joint doc):** each class mod b^k is a full AP
  above per-class onset O_r; N₀=max_r O_r (exact; verified (3,4,5) k=2/k=3). Scoped fixed-k/FINITE-onset:
  does NOT bound O_r (that's the MW kernel). The 4th ingredient in cassels' chain.

What is REFUTED / does NOT close (k-UNIFORM version = the open core, MW wall):
- N₀≤K·(d_max·d_2)^k/σ² with absolute K is FALSE: K grows 0.046→1.347→**3.759** (k=1,2,3 on (3,4,5);
  N₀(k=3)=4,330,731 verified at N=12M). No clean base (oscillates). I walked this back to cassels.
- Same wall confirmed from THREE independent angles: (1) sumset's μ(δ) value-coverage necessary-not-
  sufficient; (2) single-block stalls (consecutive-atom ratio 3>2, me+maverick); (3) sumset's window
  factor c(D,k)→∞ (c=2,15,154 for (3,4,5,6,7) k=1,2,3). Bounding c(D,k) ⟺ bounding N₀(k) ⟺ MW/Baker.

**Conclusion: no elementary proof of the k-UNIFORM strict-excess theorem; open core is MW/Baker
(cross-base power spacing |3^p−4^q|). Converges with the whole squad.** Scripts: /tmp/e124_csig2_verify.py
(k=1 clean), /tmp/e124_K_k3.py + /tmp/e124_k3_bignp.py (k=3 refutation), /tmp/e124_subset_exists.py
(minimal D), /tmp/e124_capacity_bounded.py (value-bounded c).

## (3) NEXT STEPS for a successor

1. **Finish task #17 (strict-excess theorem) with sumset** — the live breakthrough attempt. Prove the
   two-phase invariant under δ: once a contiguous interval ≥ b^k is representable, adding the next
   large atom + residue corrections keeps every subsequent integer representable, δ absorbing the
   worst-case stall at d_max-powers (maverick's ratio>2). Quantify residue-fix spare capacity vs δ.
   See sumset_strict_excess_lead.md + sumset_strict_excess_theorem.md.
2. **Observation 3 (the lift k=0⟹k≥1)** — alternative route to CLOSE condition (b): R(D,k) = "drop
   bottom k atoms per base from the k=0 system." Get Alexeev's k=0 proof (scholar/lift), check it
   survives dropping finitely many bottom atoms. NOTE sumset's [PROVED] "no black-box k=0⟹k≥1
   reduction" (CLAIMS line 64-66) — the lift proves the residue half free but NOT the full conjecture.
3. **Boundary δ=0 (incl. (3,4,7))** needs Mignotte–Waldschmidt; separate from the strict-excess theorem
   and genuinely hard (no general result since 1996).
4. **Hand the two clean lemmas to Aristotle/Lean:** lift's Residue Lemma + cassels' Lemma C.

## (4) TRAPS (cost real time — heed these)

- **FALSE CONVERGENCE:** a largest-missing value stable across a full N-doubling is NOT converged.
  (3,4,7) k2 read 785743 stably at N=1M AND 2M, but the true gap is at 3,982,888 (N≥4.1M). Safe N ≫
  d^{k+m} (modular's bound). Any k=2 threshold I/cassels/lift scanned at N≤1M is a LOWER BOUND only.
- **Naive Cassels/Brown interval-filling-from-0 is INAPPLICABLE** (min atom b^k≥3>1). Single-block
  append also stalls (ratio 3.0>2). Greedy-from-top fails (775/1419). Closure is intrinsically
  MULTI-atom. Don't re-derive these.
- **BEGL96 paper has 3 errata (+1):** Pow({3,4,5};1)=79 not 78; {3,5,7,13}=112 not 111;
  {3,6,7,13,21}=17 not 16. Trust the DP. (3,4,7)=581 is correct.
- **Lean file `erdos124.ne_zero_three_four_seven` over-claims:** tagged [solved] for ALL k, but
  BEGL96 proves only k=1 (lift verified from the PDF). Doesn't affect our open target.
