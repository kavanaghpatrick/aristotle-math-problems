# Closure-Potential Taxonomy

**Author:** Agent #2 of 10
**Date:** 2026-05-30
**Mission:** Distinguish "Aristotle's proof = real math closure" from "Aristotle's proof = bounded finite verification of a known partial result."
**Inputs:** A2 advance DNA (S1-S8), A3 failure DNA (F1-F10), A4 capability profile, Gemini WC axis (the spine: Witness Constructibility).
**Anti-target:** the rubric-points lane in `snipe_list_may30.md` that scores well on compiled_advance but produces journal-rejectable output.

The Gemini taxonomy answers *"can Aristotle compile this?"*. The Closure Taxonomy answers a strictly harder question: *"if it compiles, does it close the open conjecture, or does it close a strictly weaker thing?"* The four axes are designed to be filled in BEFORE submission so we can be honest about what a green tick will buy.

---

## Axis 1 — Closure Scope (CS): what does success actually buy us?

| Value | Definition | Decision rule |
|---|---|---|
| `full_closure` | Aristotle's theorem statement IS the conjecture, with no quantifier weakening, no domain restriction, no auxiliary decidable wrapper. | The Lean statement, after unfolding all `def`s, is α-equivalent to the formal-conjectures source statement. |
| `direction_closure` | Closes one direction of an iff or one half of an existence-uniqueness pair. The other direction stays open. | Conjecture is `A ↔ B` or `∃! x, P x`; sketch targets exactly `A → B` or existence-without-uniqueness. Closed direction must be the open one (not the trivial one). |
| `disproof_closure` | Counterexample / refutation of an open conjecture stated as universal/affirmative in the source. | Witness `w` with verified `¬ P w` where `P w` was the open conjecture's assertion. Must be against the open conjecture itself, not a strawman. |
| `bounded_version_closure` | Bounded sub-statement (e.g. for n ≤ N) of an unbounded conjecture. Infinite/general stays open. | Theorem includes `n ≤ N`, `∈ Finset.Icc a b`, or any explicit numeric ceiling on a quantifier that the source conjecture leaves unbounded. |
| `sub_claim_closure` | Closes a strict sub-statement that is independently notable (i.e. publishable as a stand-alone progress note). | Sub-statement appears in the literature as a named conjecture or as a publishable step (e.g. slot737 narrowing E647 to the Cunningham residual region). Not just a convenient bounded slice. |
| `formalization_only` | Math is already known and published; this is the Lean port. | A specific paper or textbook reference proves the result; no genuinely new mathematics is being added. Example: slot739 (Leinster D₃×C₅), slot618 (Casas-Alvero char p). |

**Excluded from the closure lane:** `formalization_only`. May still be worth submitting for engineering reasons but should never be celebrated as gap resolution.

---

## Axis 2 — Closure Mechanism (CM): how would Aristotle close it?

| Value | Definition | Aristotle demonstrated? |
|---|---|---|
| `explicit_witness` | Produce a specific number / set / graph / polynomial; verify by `decide` / `native_decide`. | **Yes** — S6 (Tuza graphs), S7 (slot618 polynomial, slot712 (1,24), slot739 D₃×C₅), S1 (slot578). |
| `bounded_to_infinite_lift` | Bounded check + a Mathlib (or in-sketch) lemma that lifts the bounded result to the infinite domain. | **Rare** — no clean precedent. Brocard would need Ferreira-effective. Slot 740 *attempts* via CRT but lift is partial (70% per E203 quotient-lift analysis). |
| `structural_finite_reduction` | Reduce an infinite claim to a finite case via parametric structure (residue classes, modular periodicity, Cunningham disjunction). | **Yes** — S3 (slot720 FT p=3 q≡71 mod 72 Fermat reduction), S5 (slot737 σ₀ multiplicativity over Cunningham split). |
| `disproof_construction` | Build an explicit counterexample (graph, witness, polynomial) and verify with `decide`. | **Yes** — S6 (Tuza 114/131/250/267), S7 (slot618), S1 (slot578, slot693). |
| `witness_table_chunked` | S2 pattern: precompute witness table externally, chunk it, `native_decide` per chunk, bridge via `Nat.nth_count`. | **Yes** — slot722, slot738. The single most reliable scaffold. |
| `density_sieve_closure` | Density/sieve argument with explicit analytic constants. | **No** — Aristotle has never closed one. Stalls at `sorry` per A4 §2 finding 9. |
| `induction_template` | Structural induction with a non-trivial decreasing measure on a hard problem. | **No** — A4 §2 finding 2: Aristotle has never invented the decreasing measure itself. |
| `none_known` | Closure mechanism is genuinely missing in literature. Research-required. | N/A — must HOLD per rubric. |

---

## Axis 3 — Closure Risk (CR): what fails between submission and closure?

| Value | Definition | Failure-DNA hook |
|---|---|---|
| `clean_decidable` | Closure rests on a decidable predicate over a finite range Aristotle has shown it can handle. | Maps to S1/S2/S3 with no F-trap exposure (slot720, slot738). |
| `partial_result_only` | High risk that Aristotle proves a bounded version and we mis-label it as closure. | F7 (bounded leak). Triggers when source claim is unbounded but the natural template is bounded native_decide. |
| `iff_rfl_trap` | Undecidable Mathlib wrappers (`Irrational`, `IsEquivalent`, `Tendsto`, `Set.Infinite`) trigger Aristotle to write `answer := <Statement>; theorem foo : answer ↔ Statement := Iff.rfl`. | F1, F8. Detected by RHS predicates in the sketch. |
| `witness_search_explosion` | `native_decide` fan-out exceeds the kernel budget; Aristotle silently narrows the range. | F9. Triggers when fan-out ≥ 10⁸ cells per chunk. |
| `definition_mismatch` | Aristotle invents a custom `def` that does not match the formal-conjectures statement. | F10. Triggers when sketch redefines `Prop` instead of importing the source. |
| `em_tautology` | Sketch states the gap as `P ∨ ¬ P`; Aristotle proves with `exact em _`. | F2. Hard-blocked by gate C6 but listed for completeness. |
| `infrastructure_overgrowth` | Aristotle produces 100+ helper lemmas and never closes the main theorem. | F3. Triggers on unbounded analytic / Pell / sieve sketches without a finite obstruction. |
| `recursive_falsification` | Witness disproves its own scaffolding. | F5. Triggers on Tuza-style apex/bridge sub-configurations of falsified-approach problems. |

A submission can have one *primary* CR. Multiple secondary risks should be listed in the feasibility certificate.

---

## Axis 4 — Honesty Marker (HM): would a math journal accept it as resolving the conjecture?

| Value | Definition | Journal-acceptable framing |
|---|---|---|
| `journal_clean` | Yes, with a reasonable scope statement in the abstract. | "We prove conjecture X" or "We disprove conjecture X via counterexample Y." |
| `journal_partial` | Bounded version is publishable as "Verified for n ≤ N" but does not close the open question. | "We verify conjecture X for n ≤ N, extending the prior bound from M to N." Counts as a research note, not closure. |
| `journal_subclaim` | A strict sub-statement (named in the literature, or a natural midpoint) is closed; closure of full conjecture remains open. | "We prove the [Cunningham-residual / 78557 / D₃×C₅] sub-case of conjecture X." Publishable as a progress paper. |
| `infrastructure_only` | Helpful scaffolding (negative shape constraints, decidability instances, residue-class enumerations) but resolves nothing stated as open. | Not publishable on its own. Lives in supplementary material or a tools paper. |

---

## The combined REAL-closure decision rule

A submission is a **REAL closure candidate** iff
```
CS ∈ {full_closure, direction_closure, disproof_closure}
∧ CM ≠ none_known
∧ CR ∈ {clean_decidable, witness_search_explosion (mitigated by chunking)}
∧ HM = journal_clean
```

A submission is a **STRATEGIC sub-claim** (worth submitting, do not over-claim) iff
```
CS ∈ {sub_claim_closure, bounded_version_closure}
∧ CM ∈ {explicit_witness, structural_finite_reduction, witness_table_chunked, disproof_construction}
∧ HM ∈ {journal_partial, journal_subclaim}
```

Everything else is `infrastructure_only` and should not be celebrated as resolving anything.

---

## Worked examples

| # | Problem | CS | CM | CR | HM | Verdict |
|---|---|---|---|---|---|---|
| 1 | **Erdős 389 bounded (Mehta table to n=50)** | bounded_version_closure | explicit_witness | clean_decidable (table is Mehta-precomputed) | journal_partial | Strategic; submit, but call it "Mehta extension", not "E389 closure". |
| 2 | **Erdős 203 lift to infinite covering** | sub_claim_closure (slot740 proved 8×8 disproof; lift opens E203 substantively) | bounded_to_infinite_lift | partial_result_only (CRT-lift 70%, F3 risk on the missing 30%) | journal_subclaim if lift completes; otherwise infrastructure_only | High-value REAL candidate IFF the lift closes. |
| 3 | **Erdős 647 unbounded (lim direction)** | full_closure (if lim is disproved) or sub_claim_closure (if only σ₀ growth bounded) | structural_finite_reduction + density_sieve | partial_result_only + iff_rfl_trap (lim is asymptotic) | journal_partial most likely | Submit slot737-sequel as sub_claim_closure; do not over-claim. |
| 4 | **slot720 (FT p=3 q≡71 mod 72, q≤1000)** | bounded_version_closure (q ≤ 1000 ceiling) | structural_finite_reduction (S3 Fermat + interval_cases) | clean_decidable | journal_partial (publishable as "FT verified for residue class, q ≤ 1000") | Already submitted; correctly classified as bounded extension, not FT closure. |
| 5 | **slot739 (Leinster D₃×C₅)** | formalization_only | explicit_witness | clean_decidable | infrastructure_only | Should NOT have been counted as gap closure. Per CLAUDE.md and MEMORY.md: known math, Lean port. |
| 6 | **Brocard `[501,1000]` (slot738)** | bounded_version_closure | witness_table_chunked (S2) | clean_decidable (chunked) | journal_partial (Brocard is unbounded; this extends the verified range) | Compiled; correctly an extension, not Brocard closure. Even `[1, 10⁶]` is still bounded_version_closure unless Ferreira-effective is invoked. |
| 7 | **Pollock tetrahedral n ≤ 343,867** | formalization_only (Pollock 1850 solved for n ≥ 343,867; bounded version is the verification of the published bound) | explicit_witness + witness_table_chunked | witness_search_explosion (F9; needs slot738-style chunking) | infrastructure_only-to-journal_partial (depending on whether the formalization counts as new) | Submit for engineering, do not celebrate as math. |
| 8 | **Riemann Hypothesis** | full_closure (target) | none_known | iff_rfl_trap (`Set.Infinite`, `Tendsto`) | infrastructure_only (any sketch will be F1) | DO NOT SUBMIT. |
| 9 | **Birch-Swinnerton-Dyer** | full_closure (target) | none_known | iff_rfl_trap + definition_mismatch (elliptic curve / L-function formalization gaps) | infrastructure_only | DO NOT SUBMIT. |
| 10 | **Tuza ν=4 (full conjecture)** | full_closure (target) | none_known (216 no-advance submissions confirm; MEMORY.md falsified list exhausted) | recursive_falsification + infrastructure_overgrowth | infrastructure_only | HOLD per rubric. Do not submit without a fresh structural diagnostic. |

---

## The single hardest distinction

`full_closure` vs `bounded_version_closure` is the load-bearing line. Aristotle's strongest scaffold (S2 witness-table chunking) reliably produces `bounded_version_closure` and we will frequently be tempted to call this "Brocard closure" or "Pollock closure". It is not, and journal HM = `journal_partial` is the honest label.

The litmus test:
> If the formal-conjectures source statement has a free `n : ℕ` and the Lean theorem replaces it with `n ∈ Finset.Icc a b` (or `n ≤ N`), it is **bounded_version_closure**, not full closure. No exceptions, including when N is the asymptotic threshold from a published effective bound — unless the sketch *also* proves the asymptotic-to-finite reduction in Lean.

This distinction is exactly the one MEMORY.md's directive #4 polices: *"Stop saying PROVEN for infrastructure that doesn't advance anything."*

---

## Integration with the feasibility certificate

Each submission's `<slot>_certificate.json` (per snipe_list rec) should add four fields:

```json
{
  "closure_scope": "bounded_version_closure",
  "closure_mechanism": "witness_table_chunked",
  "closure_risk_primary": "clean_decidable",
  "closure_risk_secondary": ["witness_search_explosion"],
  "honesty_marker": "journal_partial",
  "real_closure_candidate": false,
  "strategic_subclaim": true
}
```

The `real_closure_candidate` and `strategic_subclaim` booleans are mechanically derivable from the four axes per the decision rules above. A submission with `real_closure_candidate=false ∧ strategic_subclaim=false` should not be submitted at all (it is pure `infrastructure_only`).

---

## Authority

- Excluded-middle rule (HARD): MEMORY.md and CLAUDE.md rule 13. Any sketch with `(P) ∨ ¬ (P)` gets HM = infrastructure_only and CR = em_tautology by construction.
- Gap-targeting rule: every CS = `formalization_only` is automatically outside the closure lane, even if HM is otherwise clean.
- "compiled clean ≠ resolved the gap" (CLAUDE.md rule 12): mechanically expressed here as the requirement that REAL closure candidates have HM = `journal_clean`. `compiled_advance` alone does not satisfy this.
