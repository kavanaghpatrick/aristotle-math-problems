# sumset — HANDOFF (E124 / BEGL96 open part, erdos124.ne_zero)

## 1. PROVED / VERIFIED results + file pointers

- **Scaling reduction** `S(d,k) = d^k·B_d` (B_d = 0/1-digit base-d). One line; independently
  re-verified by troika, maverick, lift. → `sumset_reduction_scaling.md`
- **gcd(D)=1 necessity** for k≥1: prime p|gcd(D) ⟹ p^k divides every element of T_k ⟹ not
  cofinite. (Automatic at k=0.) Cross-validated by lift, maverick, troika. → same file.
- **Residue coverage (corollary):** gcd(D)=1 ⟺ T_k(D) meets every residue class mod every M.
  **⚠️ TRAP: my Lemma A is REFUTED** (modular). I claimed `(d^k·B_d) mod M = full subgroup
  gcd(d^k,M)·(ℤ/M)`; FALSE — e.g. `(3·B_3) mod 9 = {0,3}`, NOT `{0,3,6}` (6 unreachable; B_3 mod 9
  is Cantor-like {0,1,3,4}). The exact-formula Theorem B fails for gcd>1 (182 counterexamples).
  **BUT the corollary I actually use (gcd=1 ⟹ full coverage) is TRUE** — use modular's canonical
  per-prime + CRT proof (`modular_local_landscape.md` §5 / Lemma (L)), NOT my Lemma A. →
  `sumset_crt_residue_theorem.md` (needs the Lemma-A paragraph replaced; corollaries 1–3 stand).
- **Theorem C — deconvolution:** `∑_{d∈D} B_d = L_k + T_k`, L_k a FIXED finite set. The OPEN k≥1
  sumset = SOLVED k=0 sumset minus a finite Minkowski deconvolution. → `sumset_deconvolution_reduction.md`
- **Threshold growth law:** STRICT excess ∑1/(d−1)>1 ⟹ threshold = Θ((d_max·d_2nd)^k), geometric,
  C shrinks as excess grows. BOUNDARY ∑=1 ⟹ threshold ≫ (MW/Baker). → `sumset_empirical_landscape.md`
  (corrected: (3,4,7) k=2 = 3,982,888 not 785,743, per breaker; k=3 = 166,025,260 per density/breaker — NOT 57.7M, which was itself a false freeze).

## 2. Negative results (proved — save successors the dead ends)

- **No black-box reduction k=0 ⟹ k≥1.** (a) per-base scales d^k differ ⟹ the "bulk" is the SAME
  open problem, not k=0; (b) DECISIVE complexity contradiction: (3,4,7) is elementary at k=0 but
  needs Mignotte–Waldschmidt at k≥1 — a black-box reduction would make k≥1 elementary too. The
  team-lead-assigned "apply k=0 at scale" route is a PROVED dead end for closing the conjecture.
  Salvage: it proves the RESIDUE half is FREE (bounded low-power band covers all residues mod
  lcm(d^k)). → `sumset_scale_route_blocked.md`
- **Theorem B + Theorem C are NOT jointly sufficient** (explicit counterexample L={0,1,2,3},
  T=ℕ∖{powers of 10}). Confirms maverick Result 2. → `sumset_deconvolution_reduction.md`.

## 3. Work in flight + where I stopped

Main line (team-lead APPROVED): **elementary, uniform-in-k theorem for strict excess ∑1/(d−1)≥1+δ.**
Drafted the target + strategy in `sumset_strict_excess_lead.md`. Got as far as:
- exact-engine dichotomy table (strict-excess thresholds tiny & geometric vs boundary MW-large);
- last-hole anatomy: obstruction is the TWO-LARGEST-SCALE Frobenius gap, not linear-forms — e.g.
  (3,4,5,7) k=3 top hole 78,426 sits 42 below 7^3+5^7. Stopped before writing the full proof.

## 4. Precise NEXT STEPS for a successor

1. **Reconcile with maverick's negative result FIRST** (team-lead's explicit obstacle): maverick's
   inf atom-ratio = 1/(d_max−1) at powers of d_max is k-independent and seems to hit strict-excess
   families too — yet his {4,5,6,7,8} k=1 succeeded END-TO-END. Resolution hypothesis to make
   rigorous: the invariant that must dominate is the **contiguous-interval length**, NOT the raw
   atom-sum/ratio; excess δ>0 keeps the covered interval GROWING through the d_max-power stall
   points. State the theorem's hypotheses in terms of whichever invariant survives the
   maverick+lift reconciliation (they were reconciling the ratio claims at snapshot).
2. Prove: at strict excess, after each d_max-power "stall," the interval already covered (length
   ≥ next atom) lets Lemma C (cassels' step-M filling, `cassels_completeness_lemma.md`) re-fire —
   so gaps stay bounded AND the geometric law threshold ≤ C·(d_max·d_2)^k holds uniformly in k.
3. Turn "bounded gaps + all residues (modular's Lemma L)" into "gap = 0" using the δ-margin — the
   one place the boundary needs MW but strict excess (claim) does not.
4. Deliverable: `sumset_strict_excess_theorem.md` — complete proof OR honest precise statement of
   the single missing lemma. This would be a genuine publishable partial result on BEGL96.

## 5. TRAPS for the successor

- **Lemma A is false** — never cite "(d^k·B_d) mod M = full subgroup." Use modular's per-prime/CRT.
- **Sieving CANNOT prove cofiniteness** — late stragglers. (3,4,7) k=2 looked done at 785,743 (mine,
  WRONG) but true max is 3,982,888 just below 4^11; k=3 = 166,025,260 (needs N≥200M; 5.96M and
  57.7M were BOTH false freezes). Use breaker's exact engine
  (`breaker_engine2.py`), windows ≥ ~30·(d_max·d_2)^k for strict excess, FAR more at the boundary.
  Trust GAP-FINDING, never coverage. FFT-float convolution gives FALSE negatives on gaps at large N
  (I hit this) — use integer/bitmask DP.
- **Folklore density bound `density(S) ≤ ∑1/(d−1)` is FALSE** as stated (measured (3,4) density
  0.884 > 5/6). The non-cofiniteness conclusion at ∑<1 still holds via the correct mechanism
  (density's recursive top-of-d^m argument, `density_threshold_ledger.md`), not the naive bound.
- The conjecture is almost certainly TRUE; the open core is archimedean (SEED), Baker territory at
  the boundary — NOT bare-submittable to a formalizer.

Scripts: `analysis/e124q2/team/code/{cofin_check.py (exact bitset), big_check.py (numpy sieve),
density_decay.py}`. Prefer breaker's `breaker_engine2.py` for exact large-N.
