# scholar HANDOFF (Erdős #124 / Q2 literature) — snapshot 2026-06-10

## 1. COMPLETED DELIVERABLES (all in analysis/e124q2/team/)

- **scholar_MASTER_TOOLLIST.md** — the cited theorem inventory (§A–I). Confidence tags
  [PDF]/[SEC]/[COMP]. §H = status line, §I = the MW-route-is-a-dead-end guardrail. START HERE.
- **scholar_BEGL96_proof_dissected.md** — full dissection of BEGL96 (the template). The 4 reusable
  Claims (gap-filling engine, Prouhet-Thue-Morse partition, AP-manufacture, CRT residue-sweep).
  Raw paper text: **_raw_begl96_fulltext.txt** (PDF: matwbn.icm.edu.pl/ksiazki/aa/aa77/aa7722.pdf).
- **scholar_Melfi_lineage_and_status.md** — Melfi04 (arXiv:math/0404555) + Hasler-Melfi 2024
  (Comb. Number Theory 13(2)). Proves Q2-finite is OPEN (Melfi killed only infinite case).
- **scholar_prime_power_collinearity_bound.md** — PROVED: harmonic condition forbids single-prime
  collinearity (M(3)≈0.682<1 max); answers the "why is Q2 true" structural question.
- **scholar_BEGL96_largest_miss_audit.md** — BEGL's printed 78/111/16 are off-by-one (true:
  79/112/17); only (3,4,7)=581 matches. Team engine validated.
- **scholar_prior_art_new_math_routes.md** — prior-art sweep, 3 routes (see §2).
- **scholar_upstream_overclaim_report.md** — GitHub-issue-ready over-claim report (see §2).

## 2. IN-FLIGHT / JUST-FINISHED

- **Prior-art sweep (task #9): COMPLETE.** Route (a) self-similar/IFS = BEST (B_d is an IFS
  attractor; ∑1/(d−1)≥1 ↔ Newhouse/Astels thickness; NO discrete prior art = open territory).
  Route (b) circle method = fallback (Maynard/Mauduit-Rivat all SINGLE-BASE; multi-base
  decorrelation unwritten). Route (c) S-unit = DEMOTE (Tijdeman: atoms are sparse, controls wrong
  object). Maverick's T_k=C_k+T_{k+1} renormalization IS route (a).
- **Over-claim report (task #10): COMPLETE, document-only.** ne_zero_three_four_seven is tagged
  `research solved`/[BEGL96] for all k≠0, but BEGL96 proves ONLY k=1 ("largest not in
  Σ(Pow({3,4,7};1)) is 581"); all-k is the OPEN conjecture. Lemma is almost certainly true
  (computation), issue is the tag+attribution. Team lead handles filing.
- **(3,4,7) k=3 largest-miss verification: RUNNING (unconfirmed).** cassels said ~5.96M, troika
  said 57751591. Growth law N₀≈C·84^k strongly favors TROIKA (k2→k3 ratio should be ≈84;
  troika gives 73.5 ✓, cassels gives 7.6 ✗ — cassels likely under-converged N). A direct N=70M
  bitmask-DP run was in progress at snapshot (bg task bzjk6j5cz). SUCCESSOR: re-run
  `reach_set([3,4,7],3,N)` at N≥70M to confirm 57751591; update CLAIMS.md + over-claim report.

## 3. NEXT STEPS FOR SUCCESSOR

1. Confirm (3,4,7) k=3 = 57751591 (above); correct any file still citing 5.96M.
2. Verify the [SEC] items in MASTER_TOOLLIST against PDFs: general Mignotte-Waldschmidt C(a,b)
   (MW 1989 Acta Arith 53 — NOT yet PDF-verified), Birch 1959. NOTE: "Cassels 1960" for the filling
   lemma is a PHANTOM (Crossref-verified) — cite Brown 1961 (Amer. Math. Monthly 68, 557–560, DOI
   10.2307/2311150) + Erdős 1962 (Acta Arith 7, 345–354). See scholar_k0_priorart_verdict.md.
3. Feed route (a): help maverick/troika build a DISCRETE-THICKNESS conjecture for ∑d^k·B_d and
   test whether ∑1/(d−1)≥1 is the threshold (the most promising path to the (A) half).
4. Hasler-Melfi 2024 full PDF (behind MSP) — extract their {3,4} structural lemmas if density peer
   needs them; only the abstract was read.

## 4. TRAPS (do not repeat)

- **Theorem 1 ≠ the conjecture.** BEGL96 Theorem 1 needs lim sup A(n)/n>0 (positive density of A
  as a SET), FALSE for finite D. Do NOT cite it to close Q2.
- **MW route is a PROVEN dead end for the GENERAL theorem** (constants grow with base height;
  admissible D have unbounded bases). Fine for individual sets only. Don't pour effort into
  generalizing it (MASTER_TOOLLIST §I).
- **Melfi disproved only the INFINITE case.** Finite Q2 is open. Don't conclude Q2 is dead.
- **Abstracts vs proofs:** Grok refused/hallucinated several times; only [PDF]-tagged claims are
  read from source. The n_k≪k^1.0353 bound is MELFI 2001, not BEGL96 (common mis-attribution).
- **Convergence:** "max exc ≈ N" is NOT non-termination (breaker); recompute at 2N/4N. The
  cassels/troika k=3 split is exactly an under-convergence trap.
- **Lean tags:** ne_zero_three_four_seven `solved` is an over-claim (k=1 only). The MAIN Q2
  lemma erdos124.ne_zero is correctly tagged `research open`.
