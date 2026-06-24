# maverick HANDOFF (snapshot Jun 10 2026)

Role: free-agent verifier-attacker on E124-open (BEGL96 conjecture). Answer almost certainly TRUE.

## (1) PROVED / VERIFIED (with file pointers)
- **Scaling** S(d,k)=d^k·B_d — VERIFIED independently. [maverick_verify_and_k1.md]
- **Residue coverage (L)**: gcd(D)=1 ⟹ ∑d^k·B_d covers ℤ/m (14 families, k≤3, m<200) — VERIFIED. Confirms modular/lift.
- **Recursion** T_k = C_k + T_{k+1} (C_k = 2^|D| lowest-digit offsets), monotone T_{k+1}⊆T_k — PROVED+VERIFIED. = lift's §A. [maverick_recursion_engine.md]
- **inf Q1(a)/a ≈ ∑1/(d−1)**, k-independent; ≥1 ⟺ admissible (0 Cassels-filling violations for admissible; <1 only sub-threshold). [maverick_bounded_gap_lemma.md — CORRECTED]
- Cross-checks: (3,4,7) k=3 hole=166,025,260 (two doublings); (3,4,5) k=1 hole=**79** not 78; theorem_347 §B close pairs + B_7-bridges-gaps. All confirm peers.
- **(SEED) reduction** [maverick_seed_interval_pinned.md]: E124-open ⟺ full multi-atom subset-sum gap-free above finite n0(k). Scaffold all proven; open core = seed formation = MW/transcendence for general D. = team consensus.

## (2) IN-FLIGHT / verification state
- **{4,5,6,7,8} k=1**: VERIFIED cofinite from 4 (n0=3), gap-free to 1.5×10⁹. NEW instance (not in BEGL96 list).
  BUT the elementary PROOF is NOT closed — Brown's cumulative condition holds (0 violations) but proving the
  contiguity (not just the sum-bound) stalls at powers (multi-atom closure, ratio>2). **Do not promote to a
  proven elementary theorem.** Status: verified-cofinite, proof open. (Told team-lead; downgraded.)
- **My 0.25 negative result: RETRACTED.** Was a truncated-atom-list artifact (cassels: "single-ray"; me:
  "truncation bug" — same dead figure). Merged inf ≈ β ≥1 for admissible. lift's β=∑1/(d−1) is the right invariant.

## (3) NEXT STEPS for a successor
- The open core is (SEED) = "no isolated gap above n0(k)" = generalize BEGL96's (3,4,7) Mignotte–Waldschmidt
  to all admissible D. Scholar's guardrail: MW provably can't do the general ∀D case (height-growing
  constants + ∞ per-D finite checks) — so pursue scholar's 3 new-math routes, esp. **renormalization on the
  T_k=C_k+T_{k+1} recursion** (the IFS/discrete-thickness angle, scholar_prior_art_new_math_routes.md route (a)).
- For the elementary class: the right criterion is NOT "single-interval Brown" (stalls at ratio>2). Need the
  multi-atom contiguity invariant made rigorous — coordinate with cassels (Lemma C) and carry (per-class +b^k closure).
- A clean win available: rigorously prove ANY one large-d_min family cofinite via a correct multi-atom argument
  (the n0 is tiny, e.g. 3 for {4,5,6,7,8}); that would be the first elementary instance beyond BEGL96.

## (4) TRAPS + verified-vs-pending
- **TRAP — truncated atom lists**: when computing Q1(a)/sum-of-atoms-below-a, the exponent range MUST exceed
  log_{d_min}(a) or you miss dominant small-base atoms (this caused my false 0.25). Use exact geometric Q1.
- **TRAP — single-block vs multi-atom closure**: "contiguous interval extends by one atom" FAILS (consecutive
  atom ratio = d_min, >2). The real closure is multi-atom subset sums. Don't operationalize with a single interval top.
- **TRAP — window-cap artifacts**: capping the subset-sum array at N makes the "contiguous top" = N falsely;
  always verify the next atom < contiguous top before claiming closure.
- **VERIFIED**: scaling, (L), recursion, the inf≈β fact, all peer cross-checks, {4,5,6,7,8} cofinite (numerically).
- **PENDING/OPEN**: (SEED) for general D; any elementary proof (even for d_min=4); the n0(k) effective bound.

Files: maverick_FINAL.md, maverick_seed_interval_pinned.md, maverick_bounded_gap_lemma.md (corrected),
maverick_recursion_engine.md, maverick_synthesis_two_engines.md, maverick_density_exponent_is_wrong.md,
maverick_verify_and_k1.md.
