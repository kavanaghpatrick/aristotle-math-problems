# Prior-art verdict: cassels' elementary k=0 proof

**Author:** scholar. **Question (from team-lead):** is cassels_k0_elementary_proof.md (elementary
Cassels-from-0 proof that finite D, d≥3, ∑1/(d−1)≥1 ⟹ ∑_D B_d = ℕ) NEW, or known? **This gates a
publishable-note decision and a public Q1 proof-attribution.**

> **VERDICT: KNOWN (essentially) — the result is a direct corollary of Brown's criterion (1961) /
> Cassels (1960), the reduction was PUBLICLY described by Thomas Bloom in Dec 2025, and a public
> Lean proof exists (Alexeev, `Erdos124b.lean`). cassels' proof is mathematically CORRECT and a
> clean independent re-derivation, but it is NOT a new result and should NOT be published as one or
> used to claim a novel public Q1 attribution. It is a fine internal/Lean artifact.**

The earlier "no public footprint / novel in print" read (mine + Grok's first pass) was WRONG — it
missed the project's own research file `analysis/web_research_aristotle_erdos_results.md` and the
Xena blog. Correcting it now.

## The decisive evidence (verified)

1. **A public Lean proof of the k=0 case already exists.** Boris Alexeev, `plby/lean-proofs`,
   `src/v4.24.0/ErdosProblems/Erdos124b.lean` (407 lines, late 2025). Per the project's own audit
   (`web_research_aristotle_erdos_results.md`, lines 91–100): it "reproves Brown's criterion from
   scratch … constructive `u_seq` greedy sequence + base-d digit decomposition for subset-sum
   representation." **That greedy `u_seq` + base-d digit decomposition IS cassels' atom-filling
   argument.** Same proof.

2. **Thomas Bloom (the erdosproblems.com author) PUBLICLY described exactly cassels' proof** in the
   comments of Alexeev's Xena Project blog post (xenaproject.wordpress.com/2025/12/05/, verified via
   WebFetch). Bloom characterises the proof as following *"the obvious inductive way that generalises
   what works for powers of 2,"* reducing to *"just a single inequality,"* and explicitly says he
   *"hasn't learnt anything new about the notion of completeness"* from it. cassels' proof is exactly
   "the obvious induction reducing to a single inequality" (the inequality being ∑1/(d−1)≥1). So the
   database maintainer himself has already published this characterisation.

3. **The underlying lemma is classical = "Brown's criterion"** [Crossref-VERIFIED: J. L. Brown Jr.,
   "Note on Complete Sequences of Integers", Amer. Math. Monthly 68 (1961) 557–560, DOI
   10.2307/2311150]: a strictly increasing (aₙ), a₁=1, with a_{n+1} ≤ 1 + ∑_{i≤n} aᵢ ⟹ every nonneg
   integer is a sum of distinct aₙ. This is the interval-filling lemma the proof uses. Follow-up:
   **P. Erdős, Acta Arith. 7 (1962) 345–354, DOI 10.4064/aa-7-4-345-354.**
   ⚠⚠ PHANTOM-CITATION CORRECTION (Crossref-verified, supersedes earlier cautions): the
   "J.W.S. Cassels 1960 / Acta Sci. Math. Szeged 21, 111–124" reference circulated for this lemma
   DOES NOT EXIST — it is a conflation with the Erdős Acta Arith. 7 (1962) paper above (Erdős not
   Cassels; Acta Arith not Szeged; 1962 not 1960). Cassels's real 1960 "On a conjecture of Bush"
   (Proc. Camb. Philos. Soc.) note does NOT contain the criterion. **Cite Brown 1961 (safest,
   earliest confirmed) + optionally Erdős 1962; DROP all "Cassels 1960" references.** The criterion
   is essentially classical/folklore.

## What this means for the team's standing claims

- The earlier statement (mine, in several files) "Alexeev's k=0 proof has NO public footprint" is
  FALSE — correct it. The footprint is: Erdos124b.lean (407 lines, public) + Alexeev's Xena blog +
  Bloom's comment + Tao's commentary. The k=0 case is a publicly-resolved, publicly-explained,
  publicly-formalised result whose proof is the Brown/Cassels induction.
- cassels' proof is a CORRECT independent re-derivation (and the "stronger contiguous-from-0 form"
  is what Brown's criterion gives anyway — Brown yields "every nonneg integer", i.e. from 0). It is
  NOT stronger than the public proof in any essential way.
- **Tao/Alexeev's documented point:** the actual scientific content of "solving #124" was *noticing
  that Erdős's restated 1996/1997 hypothesis dropped a key assumption, making the problem a corollary
  of Brown's criterion* — i.e. the result is easy ONCE you see it's a completeness problem. The hard
  problem is the BEGL96 k≥1 conjecture (our Q2), which remains open.

## Recommendation

- **Do NOT** file cassels' proof as a novel result or claim a new public Q1 attribution. The public
  attribution already exists (Erdős restatement → Aristotle/Alexeev → Brown's criterion; Bloom's
  characterisation).
- **DO** keep cassels' proof as the team's internal/Lean base case for the k≥1 lift (its real value:
  it cleanly locates the k=0→k≥1 gap at the loss of the 1-atom seed + the d^{1−k} density decay —
  that diagnostic IS useful for the open Q2 attack).
- **For modular's dossier #1 / any Aristotle submission:** the k=0 case is DONE and known — do not
  submit it as open. Only the k≥1 (Q2) target is open.
- If the team still wants a written note, it can only be an *expository/formalization* note ("an
  elementary proof of the s=0 case", explicitly crediting Brown/Cassels + Alexeev + Bloom), NOT a
  research claim. Low value given Bloom already described it.

## One genuinely-open novelty thread (salvage)

The k≥1 statements are NOT corollaries of Brown's criterion (the merged atom sequence is NOT
Cassels-from-0 once the d^0=1 seed is gone — cassels' own §"what it does not give"). So a rigorous
elementary theorem for the STRICT case ∑1/(d−1) > 1 at k≥1 (if achievable, per the discrete-thickness
program) WOULD be new — Brown/Cassels does not reach it. That, not the k=0 case, is where a
publishable advance could live.
