# Full plby/lean-proofs sweep for E124 prior art

**Author:** scholar. **Method:** authoritative — `gh api` over the full repo tree (511 files) +
read the actual Erdos124b.lean source. **Verdict: the repo contains ZERO prior art on Q2 / k≥1 /
(3,4,7)-for-k≥2 / strict-excess. The only E124 file is Erdos124b (the k=0 "former statement").**

## Inventory (complete)

`gh api repos/plby/lean-proofs/git/trees/main?recursive=1` → 511 files. ALL E124-adjacent files:
- `ErdosProblems/Erdos124b.md` — note: "a formalized proof of the FORMER statement of Erdős
  Problem 124."
- `src/latest/ErdosProblems/Erdos124b.lean` (643 lines, Lean v4.29.1)
- `src/v4.24.0/ErdosProblems/Erdos124b.lean` (same, pinned version)

**There is NO `Erdos124a`, no k≥1 file, no (3,4,7) file, no strict-excess file.** (An `Erdos347.lean`
exists but is Erdős Problem **347**, unrelated to our (3,4,7) triple — a "347" false hit; flagged so
nobody confuses it.) The only completeness-adjacent non-124 file is a PrimeNumberTheoremAnd
consequence file, irrelevant.

## What Erdos124b.lean actually proves (read in full)

The `k` in the file is the NUMBER OF BASES (`Fin k → ℕ`), NOT an exponent floor. The digit condition
is `((d i).digits (a i)).toFinset ⊆ {0, 1}` with **NO exponent lower bound** ⟹ this is the **k=0 /
s=0 case** (the Erdős "former statement", = our Lean `erdos124.zero`). Lemma roster:
- `algebraic_gap` — **literally cassels' key estimate**: `m ≤ 1 + ∑ (y_i−1)/(d_i−1)` under
  `1 ≤ ∑ 1/(d_i−1)`. Same inequality as cassels_k0_elementary_proof.md's `S(X) ≥ (m−1)∑1/(d−1) ≥ m−1`.
- `browns_criterion` — **Brown's criterion, explicitly named** (line 70). CONFIRMS my prior-art
  verdict that the k=0 proof IS Brown's criterion. Not Cassels.
- `u_seq_*`, `chosen_exponent`, `digits_of_subset_sum_u_seq` — the greedy merged-atom sequence +
  base-d digit decomposition (= cassels' merged-atom interval-filling, formalized).
- `erdos_conjecture_true`, `erdos_124`, `formal_conjectures_erdos_124(_corrected)` — the main
  theorems. Clean: `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`, no `sorry`.
- Note: the file CORRECTS the formal-conjectures "≥1" to "=1" (`formal_conjectures_erdos_124_corrected`)
  — Alexeev's own observation that the stated hypothesis needed the equality form for the s=0 reading.

## Consequences

1. **k=0 prior-art verdict REINFORCED, now airtight:** the public Alexeev/Aristotle proof uses
   `browns_criterion` + a merged greedy sequence + base-d digit decomposition = exactly cassels'
   argument. cassels' k=0 proof is the same known result. (CITE: Brown 1961; NOT the phantom
   "Cassels 1960" — see scholar_k0_priorart_verdict.md.)
2. **Q2 / k≥1 is NOT in the repo.** No exponent-shifted statement, no (3,4,7)-for-k≥2, no
   strict-excess family is formalized or claimed anywhere in plby/lean-proofs. So the repo poses no
   prior-art collision for our k≥1 work. (This is a clean negative — the most likely surface is
   exhausted.)
3. The header "Formalization status: Partial" = only the k=0 former statement is done; the BEGL96
   k≥1 conjecture is untouched there too. Consistent with the rest of the literature (Q2 open).

---

# Prior-art checks (2) & (3): the strict-excess k≥1 theorem and the (3,4,7)-all-k bridge

Both checked via live search across Brown-descendants, Hegyvári corpus, Birch, Melfi/Hasler-Melfi,
arXiv, and the plby repo (above). **Both verdicts: NEW relative to the searched literature** — with
the standard caveat (the k=0 case "looked novel" too until the public Lean proof surfaced; but here
the strongest single negative IS confirmed — plby/lean-proofs, the most likely surface, has nothing
on k≥1).

## (2) Strict-excess k≥1 theorem — VERDICT: NEW (verify-pending)
Statement: D finite, d≥3, ∑1/(d−1) > 1 (strict), gcd=1, k≥1, with "margin δ dominates worst-pair
log-clustering" ⟹ ∑ d^k·B_d cofinite. Findings:
- Brown 1961 + all immediate follow-ups: k=0 (unshifted) ONLY; no exponent-lower-bound extension.
- Hegyvári ("On complete sequences", Acta Math. Hungar.; "On the representation of integers as sums
  of distinct terms from a fixed set", Acta Arith. 92 (2000) 99–104; later subset-sum papers): general
  fixed sets / density criteria, NEVER the truncated geometric family {d^j : j≥k}, no strict
  ∑1/(d−1)>1 threshold.
- Birch 1959: {p^i q^j} unshifted only; no published (i,j≥s) version.
- No paper found stating a strict-excess sufficient condition that reduces to Brown at k=0 and holds
  for k≥1. **NEW.**

## (3) (3,4,7)-for-all-k theorem + its mechanism — VERDICT: NEW (k=1 is BEGL96-known)
Statement: ∀k≥1, 3^k·B_3+4^k·B_4+7^k·B_7 cofinite (= theorem_347_allk.md). Findings:
- (3,4,7) cofinite for ALL k≥1: NOT published. BEGL96 = k=1 only (largest hole 581). Hasler-Melfi
  2024 = {3,4} density only, says nothing about the triple at any k.
- Mechanism (A) digit recursion R_k = C_k + R_{k+1} (= IFS self-similarity, B_d={0,1}+d·B_d): the
  underlying IFS description is folklore (Erdős–Joó–Komornik etc.) but the concrete 3-base recursion
  used to LIFT completeness k=1→all-k is not published.
- Mechanism (B) MW-bad-pairs k-uniformity (close (3^p,4^q) pairs = convergents of log4/log3,
  independent of k; raising k discards only finitely many): NOT published anywhere. BEGL used the MW
  bound at k=1 only.
- **NEW** — the theorem and both mechanism components are unpublished. theorem_347_allk.md is a
  genuine new result (modulo §C's transcendence input being supplied at full rigor).

⚠ CAVEAT (apply the k=0 lesson): these are "could not find it" verdicts. Grok's bibliographic details
are unreliable (it mis-cited BEGL96 pages as 65–72; correct is 133–138). The substantive "not
published" conclusion is consistent across multiple independent checks AND the authoritative plby
repo sweep, so confidence is reasonably high — but a maintainer should confirm against MathSciNet/
zbMATH forward-citations of BEGL96 before any publication claim. The one real risk is an obscure note;
the major journals/authors are covered.
