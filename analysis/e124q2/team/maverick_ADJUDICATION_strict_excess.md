# maverick ADJUDICATION: the per-fixed-k strict-excess theorem dispute — VERDICT

Per team-lead order. Settles cassels+lift+modular+carry ("closes elementarily") vs sumset ("no
elementary proof, even strict") vs density ("needs gcd(d_max,d_2nd)=1"). Note: cassels' and sumset's
LATEST files have already largely converged toward "no" — the live load-bearing claims are lift's
Lemma B and the k=1 sub-claim. I attacked the three specified checks.

## VERDICT: **NOT-A-THEOREM** (as a general-k elementary theorem). Breakdown by tier:
- **General-k strict-excess cofinite, elementary:** NOT PROVEN. (the disputed flagship)
- **k=1 strict-excess, elementary:** CONDITIONAL — needs the unproven hypothesis gcd(d_max,d_2nd)=1
  (density is right); even then the bound constant is fitted, not derived.
- **Non-minimal strict-excess D, all k (Lemma M):** PROVEN (the one genuine elementary survivor).

## CHECK (1): is lift's "Lemma B" PROVEN or empirical-dressed-as-lemma?
**SPLIT.** lift's Lemma B = an exact structural IDENTITY + an unproven bound:
- IDENTITY "N₀ = max_r O_r" (per-class onset): PROVEN — but trivially, it's true by definition of O_r.
  Not load-bearing content; it's a restatement.
- The CONTENT "within-class gaps close by elementary density from m₀" (step 2): **NOT PROVEN.**
  I tested (3,4,5) k=1: class onsets are 63, 79, 74 — they EXCEED Lemma A's m₀=37 by ~2×. So "gaps
  close by m₀" does NOT describe what happens; the within-class closing is LATER and m₀ does not bound
  it. The inference "min#reps grows ⟹ value-holes close" IS the coverage-blind-to-internal-gaps trap
  the lead suspected: a hole is a point where reps=0 regardless of the surrounding trend, and the
  growing-mean does not bound the LAST hole's position. **Lemma B's load-bearing half is empirical.**
  (lift's own file concedes this: "Lemma A' is the genuine remaining content... OPEN for general k.")

## CHECK (2): does the claim cover {3,4,6}, or silently need gcd(d_max,d_2nd)=1?
**SILENTLY NEEDS gcd(top-two)=1.** Tested carry's k=1 bound N₀ ≤ 0.27·C'/σ²:
| D | σ | true N₀(k=1) | bound | holds? | gcd(top2) |
|---|---|--------------|-------|--------|-----------|
| (3,4,5) | .083 | 79 | 159 | ✓ | 1 |
| (3,4,5,7) | .25 | 22 | 23 | ✓ | 1 |
| (3,5,7,9) | .042 | 112 | 784 | ✓ | 1 |
| **(3,4,6)** | .033 | **986** | **980** | **✗** | **2** |
{3,4,6} is the ONLY gcd(top2)≠1 family and the ONLY one that VIOLATES the bound (986>980). Root:
gcd(6,4)=2 with 6=2·3 ⟹ |2^a−3^b| clustering. So the k=1 claim does NOT cover {3,4,6} and density's
gcd(d_max,d_2nd)=1 hypothesis is REQUIRED (silently assumed). [Matches my earlier v8 finding: {3,4,6}
has C growing 41→420→3000.] Also: the bound is violated by a razor margin (986 vs 980), so the
constant 0.27 is FITTED, not derived — fragile even for gcd(top2)=1.

## CHECK (3): [PROVEN] vs [VERIFIED-EMPIRICALLY] ledger
| claim | status |
|---|---|
| Lemma A: S(X) ≥ m·β − C' | **PROVEN** (re-derived) |
| Corollary: global gap-condition for m ≥ m₀=(C'−1)/σ | **PROVEN** |
| Identity N₀ = max_r O_r | PROVEN (structural, trivial) |
| Residue coverage gcd=1 ⟹ all classes mod M | **PROVEN** |
| Lemma B step 2: within-class gaps close by density from m₀ | **NOT PROVEN** (onsets exceed m₀ 2×) |
| Lemma A': O_r ≤ K·(scale)^k, K absolute | EMPIRICAL k≤2 only; K diverges 0.05→1.35→3.76 at k=1,2,3 |
| k=1 bound N₀ ≤ 0.27 C'/σ² | EMPIRICAL+FITTED; FAILS {3,4,6}, needs gcd(top2)=1 |
| Lemma M: non-minimal D reduce | **PROVEN** (trivial, real) |
| General-k strict-excess cofinite | **NOT PROVEN** (K-divergence = MW wall) |

## WHAT TO SHIP (recommended honest statements; writeup currently HELD)
1. **PROVEN, ship:** Lemma A (gap-condition with explicit m₀=(C'−1)/σ; gap-condition HOLDS for σ>0,
   FAILS at σ=0 — the clean strict/boundary split, mechanism-explicit). Lemma M (non-minimal
   reduction). Residue coverage. The k=0 theorem (separate, Brown — fully proven).
2. **CONDITIONAL, label as such:** "strict-excess (σ>0) ⟹ cofinite ∀k, CONDITIONAL on Lemma A'
   (per-class onset O_r ≤ K·scale^k, K absolute)" — and Lemma A' is OPEN (K diverges empirically at
   k=3; = the MW wall). Do NOT call this a theorem.
3. **DO NOT SHIP** any "per-fixed-k strict-excess closes elementarily" claim — checks 1+2+3 refute it.

## CITATION FIX (enforced)
Replaced phantom "Cassels 1960" → **Brown 1961 + Erdős 1962** wherever the interval-filling /
complete-sequence lemma is cited. Files touched in my workspace: maverick_k0_elementary_proof.md,
maverick_INVENT_bridge.md, maverick_ASSAULT_thickness.md, CLAIMS.md. Flagging cassels/lift/sumset to
do the same in theirs (the "Cassels interval-filling lemma" is properly Brown 1961, "Note on a problem
of Erdős and Heilbronn"-lineage / Erdős 1962 complete-sequence; J.W.S. Cassels has no such 1960 paper
in this lineage — phantom).

---

# EXTENSION (team-lead order): density's theorem + ONE canonical statement across all 3 versions

## density's "finalized" strict-excess theorem: REFUTED as stated + mislabeled

**Claim (density):** gcd(D)=1, ∑1/(d−1)>1, gcd(d_max,d_2nd)=1 ⟹ N₀ ≤ C(δ,D)·(d_max·d_2nd)^k, C
k-independent, "transcendence-free."

**REFUTED on {3,4,5}** (which satisfies ALL three hypotheses: gcd(3,4,5)=1, ∑=1.083>1, gcd(5,4)=1 —
squarely IN density's scope). Adequate-window N₀ (truncation-guarded, lm<N/2):
| k | N₀(3,4,5) | N₀/(d_max·d_2)^k = N₀/20^k |
|---|-----------|---------------------------|
| 1 | 79 | 4.0 |
| 2 | 77,613 | 194 |
| 3 | 4,330,731 | 541 |
N₀/20^k GROWS 4→194→541 (×49, ×3). For density's bound to hold C must grow with k, but C=C(δ,D) is
claimed k-INDEPENDENT. **So the theorem as stated is FALSE** — the (d_max·d_2nd)^k scale is simply
wrong; N₀ grows faster. (Exactly sumset+carry's joint data.) gcd(top-two)=1 is NECESSARY (kills the
{3,4,6} corner) but NOT SUFFICIENT — {3,4,5} has it and still violates the bound.

**MISLABEL "transcendence-free":** density's own proof (density_strict_excess_thickness_margin.md
lines 149, 157) INVOKES a "Baker floor" — Baker's polynomial lower bound on |d_max^a − d_2nd^b| — to
argue c(D) is bounded. Baker's theorem (linear forms in logs) IS transcendence input. Calling the
result "transcendence-free" while the proof rests on a Baker bound is an internal contradiction. The
correct label is **Baker-CONDITIONAL** — a weaker but still real claim: the threshold CONSTANT is
controlled by a Baker lower bound, which exists but is ineffective/non-elementary.

## THE ONE CANONICAL STATEMENT (all three versions reconciled)

What is actually proven about strict-excess E124 (∑1/(d−1) > 1, gcd(D)=1), unified:

| Component | Hypotheses | Status |
|---|---|---|
| **Lemma A** (gap-condition holds for m ≥ m₀=(C'−1)/σ) | σ>0 | **PROVEN** (elementary; cassels, I re-derived) |
| **Residue coverage** (all classes mod M hit) | gcd(D)=1 | **PROVEN** (modular) |
| **Lemma M** (non-minimal D reduce to a proper admissible subset) | D has a proper admissible subset | **PROVEN** (elementary, trivial; sumset/carry; 72/115 strict families) |
| **k=0 case** (∑B_d = ℕ) | ∑1/(d−1)≥1 | **PROVEN** (Brown 1961; separate, fully elementary) |
| **k=1 threshold bound** N₀≤0.27C'/σ² | σ>0 AND gcd(d_max,d_2nd)=1 | **EMPIRICAL+FITTED** (fails {3,4,6} w/o the gcd hyp; razor margin even with it) |
| **General-k, gcd(top-two)=1** N₀≤C·(d_max·d_2)^k | density's | **FALSE as stated** (refuted {3,4,5}); salvageable only as **BAKER-CONDITIONAL** with C growing |
| **Per-fixed-k closes elementarily** (cassels/lift Lemma B step 2) | σ>0 | **NOT PROVEN** (onsets exceed m₀ 2×; coverage-blind-to-internal-gaps) |
| **Minimal D, general k cofinite** | minimal admissible | **OPEN** (= MW/Baker wall) |

## ⟹ HONEST UNIFIED STATEMENT (the durable structural truth, ship THIS):
> **Strict-excess E124 splits cleanly (Lemma M):**
> - **NON-MINIMAL D** (has a proper admissible subset): cofinite for all k, **PROVEN ELEMENTARY** —
>   Lemma M reduces to the subset; the subset's cofiniteness propagates by 0∈d^k·B_d. (72/115 strict
>   families; max k=1 threshold 74.) This is the durable structural truth the lead identified.
> - **MINIMAL D** (no proper admissible subset; the 43/115, including all {3,4}-clustering cases):
>   **OPEN** — the threshold's k-growth is governed by cross-base power-spacing (MW/Baker), NOT by any
>   elementary f(δ,D,k). Confirmed from both sides (cassels onset-growth K: 0.05→1.35→3.76; sumset
>   N₀/scale^k: 4→194→541).
>
> Plus, separately PROVEN: the k=0 theorem (∑B_d=ℕ, Brown), Lemma A (gap-condition + explicit m₀,
> giving the clean σ>0 vs σ=0 split), residue coverage. CONDITIONAL: k=1 needs gcd(top-two)=1 (Baker
> floor, not transcendence-free). NOT a theorem: "per-fixed-k closes elementarily," "all strict excess
> with C constant."

## CITATIONS: Brown 1961 + Erdős 1962 (NOT phantom "Cassels 1960"); density's "Baker floor" must be
labeled as the transcendence input it is (Baker-conditional, not transcendence-free).
