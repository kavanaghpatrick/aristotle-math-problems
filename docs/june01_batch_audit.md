# June 1-7 Batch Audit — Feasibility Filter (Agent #10)

**Auditor**: Agent #10 of the May 30 batch-prep team. Audit performed against `/Users/patrickkavanagh/math/docs/feasibility_filter_rubric.md` (v1.0).

**Audit scope**: All sketches in `/Users/patrickkavanagh/math/submissions/sketches/` newer than `docs/debate_results_may30.md` (i.e., drafted during this batch-prep window).

**Sketches audited**: 8 found at first polling; the 9th sibling agent did not produce a sketch within the polling window (4+ minutes of stability after the 8th draft landed). Audit proceeds on the 8 produced. If the 9th appears, append to this table.

---

## Audit Procedure (per sketch)

1. Run `check_gap_targeting()` from `scripts/safe_aristotle_submit.py`. Record PASS / FAIL.
2. Read sketch + (if present) `_ID.txt` companion.
3. Classify under the five rubric categories.
4. Verify entry conditions:
   - `mechanical-extension`: parent slot cited; no break point in new range.
   - `constructive-search`: recipe named.
   - `structural-open`: fresh diagnostic file or new modular obstruction exists.
   - `known-formalization`: would be HOLD.
5. Cross-check `failed_approaches` table for resurrected approaches.
6. Recommendation: **BATCH** / **HOLD** / **REWORK**.

---

## Audit Table

| # | Sketch | Gate | Category | Novelty | Entry Condition | Recommendation | Reasoning |
|---|---|---|---|---|---|---|---|
| 1 | `FT_p3_q71_family_first_failure.txt` | PASS (gap_targeting, 19 ln) | `mechanical-extension` (degraded) → **structural-open** | mechanical extension into a known-break-point range | slot720/slot736 parent skeleton — but the new range q ≤ 10000 contains 8 prime-A break points {1583, 2663, 3671, 4751, 5039, 6047, 6551, 9719}. The sketch acknowledges the break and asks Aristotle to find a SINGLE proof covering both small-divisor AND prime-A cases. That is a NEW mechanism, not a mechanical extension. The supporting diagnostic file `analysis/ft_q1583_diagnostic.md` exists and confirms the theorem is structurally true at q=1583 via the LARGE-prime instantiation. Fresh diagnostic = yes. | **BATCH** | This is exactly what the rubric's `structural-open` entry condition allows: a fresh structural diagnostic (the May 30 prime-A scan + ft_q1583_diagnostic) identifies a new computable subclaim (instantiate `not_dvd_via_fermat_factor` with r = A(q) itself). The submission asks Aristotle to unify two mechanisms under one theorem. High novelty. Caveat: this overlaps significantly with #4 (FT_p3_q1583_alternate); see deduplication note. |
| 2 | `FT_p3_q1583_alternate.txt` | PASS (gap_targeting, 21 ln) | `constructive-search` | half-novel | Diagnostic complete (`ft_q1583_diagnostic.md`): direct computation gives 3^1583 mod 2507473 = 1702700 ≠ 1, ord_3 = 208956. Recipe explicit: instantiate the slot720 helper with r = A(1583). | **BATCH** | Single-point diagnostic test of the proof mechanism at the canonical break. Tightly scoped, fully computable, clear novelty (extends slot720's mechanism by a 2nd-mode witness rather than a bound bump). Better-targeted than #1 because it isolates ONE q rather than a range with 8 breaks. **If batch capacity is 5, prefer #2 over #1** — #1 is the same idea but a strictly harder formalization. |
| 3 | `erdos647_cunningham_residual_35.txt` | PASS (gap_targeting, 20 ln) | `finite-verification` (with constructive witnesses) | novel | Bounded universal over 35 enumerated n; supporting table `analysis/erdos647_cunningham_witnesses.json` has explicit witness m = n-5 or n-6 with offset histogram {5: 27, 6: 8} and σ₀ values. Per-case witness lookup → `native_decide` cascade in slot738 style. | **BATCH** | Highest-confidence submission of the batch. Closes the entire E647 failure region up to 10⁶ when combined with slot737. Genuinely novel because it CLOSES a major open conjecture's bounded version. Recipe is unambiguous. Risk: kernel performance on 35-row witness table is well within slot738's demonstrated headroom. |
| 4 | `erdos647_density_extension.txt` | PASS (gap_targeting, 19 ln) | `finite-verification` (with constructive witnesses) | novel — DUPLICATE | Same supporting data as #3 (n-5 / n-6 witnesses). The framing is broader (n ∈ [25, 10⁶] unified statement, asserting E647 is *false* on the bounded range) but the proof obligation reduces to slot723 + slot737 + the 35 Cunningham witnesses. | **HOLD (dedup)** | This is functionally a unified-statement version of #3 plus slot723/slot737 reassembly. Submitting both #3 and #4 wastes a slot — they share the same novel content. **PREFER #3** (the residual-only target) because it lets the slot723/slot737 advances stay attached as context cleanly; #4 forces re-derivation of those advances. If batch capacity allows only 5, drop #4. |
| 5 | `erdos203_grid_12x12_B1000.txt` | PASS (gap_targeting, 22 ln) | `constructive-search` (with falsification fallback) | novel | Fresh diagnostic = `analysis/erdos203_quotient_lift_may30.md`. It proves slot740's 22-prime cover does NOT lift (~70% quotient coverage) AND further shows that for slot740's specific m, no index-1 prime ≤ 2000 catches the 23 missing 12×12 cells. This sharpens the question: does ANY m admit a 12×12 cover with B=1000 primes? Either Aristotle finds one (constructive) OR proves impossibility (sharper than the 8×8 disproof). | **BATCH** | Excellent gap-targeting: built on slot740's empirical reality + lift analysis. Genuine novelty because either outcome advances Erdős 203 understanding. The bound increase from B=500 to B=1000 plus grid increase from 8×8 to 12×12 is well-motivated by the lift analysis. Risk: Aristotle may produce another finite-grid artifact — but that's the point of the experiment. |
| 6 | `erdos203_sierpinski_1d_benchmark.txt` | PASS (falsification, 20 ln) | `constructive-search` | half-novel | Pure benchmark of slot740 methodology in 1D. Index-1 primes (2 primitive root mod p): the smallest few Artin primes (3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67…). Density Σ 1/(p−1) over Artin primes diverges; ⌈32/(p−1)⌉ summed exceeds 32, so a covering m exists. Recipe is exactly slot740's: greedy partition + CRT. | **BATCH (low priority)** | Methodologically useful — tests whether the slot740 mechanism is robust beyond the specific 2D 8×8 case. If kernel succeeds, validates the methodology; if it fails, exposes hidden 2D-specific assumptions. Not novel mathematics per se (1D Sierpinski-style coverings have been studied since 1960), but a methodological probe. Place in batch only if a slot remains after the 4 higher-priority targets. |
| 7 | `brocard_nrange_1001_2000.txt` | PASS (gap_targeting, 19 ln) | `mechanical-extension` | mechanical | Parent slot738 (Brocard [501, 1000]); skeleton transfers verbatim with 20-chunk × 50-entry cascade vs slot738's 10×50; no known break point. Methodology proven scalable up to p_1001² = 6.27×10⁷; this submission tests p_2001² = 3.03×10⁸ (4.8× larger sieve). | **BATCH** | Canonical `mechanical-extension`. The May 30 debate's three AIs all agreed: one mechanical calibration slot is acceptable. Brocard [1001, 2000] is the agreed-upon choice. Use this as the calibration slot for the encoding refactor's headroom. |
| 8 | `brocard_structural_intermediate.txt` | PASS (gap_targeting, 22 ln) | `mechanical-extension` (aggressive) → **REWORK** | half-novel | Same parent slot738, but a 10× range jump (n ∈ [1001, 10000]) vs the conservative 2× bump in #7. Sketch hand-waves the encoding scaling (200-chunk × 50-entry "or equivalent restructuring"). The "structural intermediate" framing suggests novelty, but the proof obligation is the same `native_decide` cascade — just bigger. | **REWORK or HOLD** | Two problems: (a) two Brocard slots in one batch is metric-hacking (slot738 + #7 + this = three of the last four batches on the same mechanical lane); (b) the 10× scaling is not pre-validated. The slot738 encoding has demonstrated headroom but not 10×. Recommend: drop this submission; if the Brocard mechanical slot ever scales beyond #7, do it incrementally in the next batch after #7's runtime data lands. Alternatively: keep #8, drop #7 — but #7 is the safer choice per the May 30 consensus. |

---

## Summary Classification

| Category | Count | Sketches |
|---|---|---|
| `finite-verification` | 2 | #3, #4 (dedup → 1 effective) |
| `constructive-search` | 3 | #2, #5, #6 |
| `mechanical-extension` | 2 | #7, #8 (recommend keep #7, drop #8) |
| `structural-open` (with diagnostic) | 1 | #1 |
| `known-formalization` | 0 | (none — Leinster correctly excluded) |

## Recommended Batch (5 slots, per depth-over-breadth directive)

If the batch capacity is 5, the recommended slate is:

1. **#3 — erdos647_cunningham_residual_35** (highest confidence; closes E647 bounded)
2. **#5 — erdos203_grid_12x12_B1000** (highest novelty upside via slot740-lifted diagnostic)
3. **#2 — FT_p3_q1583_alternate** (single-point novelty diagnostic at the canonical break)
4. **#7 — brocard_nrange_1001_2000** (one mechanical calibration slot, per consensus)
5. **#6 — erdos203_sierpinski_1d_benchmark** (methodology probe; cheap)

**Dropped from batch**:
- **#1 (FT_p3_q71_family_first_failure)**: superseded by #2 — same mechanism, harder formalization, no clear gain.
- **#4 (erdos647_density_extension)**: duplicate of #3 — same content, broader statement, wasted slot.
- **#8 (brocard_structural_intermediate)**: aggressive scaling not pre-validated; #7 is the safer mechanical pick.

---

## Specific Red Flags

- **None of the 8 sketches resurrect a falsified approach** from the `failed_approaches` table. (Tuza ν=4 entries dominate that table; no E647/E203/FT/Brocard entries triggered.)
- **None of the 8 sketches are `known-formalization`** — the Leinster lane correctly dropped per debate consensus. No agent attempted to re-formalize the D₃ × C₅ witness or any other solved 2001/2003 result.
- **No EM-tautologies** detected — the gap-targeting gate's C6 check would have caught them at submission anyway, but all 8 sketches state existence OR impossibility separately, not the disjunction.
- **`structural-open` smuggling check**: #1 came closest to smuggling — it labels itself as a family extension (mechanical-extension framing) but is in fact a structural reformulation. The audit reclassifies it. It still passes because the supporting diagnostic exists, but if the diagnostic file were absent this would be REWORK.

## Specific Concerns Worth User Attention

1. **#5 (E203 12×12)** is the most novelty-rich submission of the batch. The lift analysis already shows slot740 does not lift; this submission converts a "search for impossibility" into a "search for either existence or sharper impossibility." Either way the result is informative. This is the slot740 → next-iteration path.
2. **The FT branch (#1, #2)** has TWO sketches targeting overlapping content. Pick ONE — #2 is tighter.
3. **The Brocard branch (#7, #8)** also has two sketches. Pick ONE — #7 is safer.
4. **The 9th sibling agent**: produced no sketch within the polling window. Their absence does not block the batch; just note it.

---

## Methodology Note for Future Audits

This was the first audit under the Feasibility Filter rubric. Observations:

- The rubric correctly classifies 8/8 sketches without ambiguity.
- The 5-category split (vs the May 30 debate's proposed 4) is useful: `mechanical-extension` distinguishes slot738-style range bumps from full `finite-verification` work like the Cunningham closure.
- The `structural-open` entry condition is THE critical filter — without it, #1 would have looked like a casual mechanical bump and slipped through. With it, the audit demands the supporting diagnostic file and either approves (it exists) or holds.
- No sketch failed `check_gap_targeting()`. The drafting agents have internalized the C1-C6 hard rules from prior batches.

Outcome: 5 recommended for batch submission, 3 recommended HOLD/REWORK or dropped as duplicates.
