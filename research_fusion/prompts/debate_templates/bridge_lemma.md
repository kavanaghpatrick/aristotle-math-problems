# Bridge Lemma — Decomposing the Gap Between Known and Unknown

**Purpose:** Identify a SINGLE bridge lemma that, if proved, would close the open problem by composing with one or more existing theorems. The aim is to factor the problem into "known theorem(s) + one specific unproven lemma."

**When to use:**
- Want to scope a 1-week proof attack, not a 1-year program
- Need to know what to submit as the next bare gap
- Suspect the problem is "almost closed" but missing one step
- Need to convert vague intuition into a concrete sub-problem

**Output shape:** 1-3 candidate bridge lemmas per AI per round, each with: lemma statement, the existing theorem(s) it composes with, the explicit "gap-between-them" that the lemma closes, and a feasibility estimate.

**Difference from technique_scout:** technique_scout proposes new tools; bridge_lemma proposes a NEW PROPOSITION that, combined with EXISTING tools, closes the gap. Often the bridge lemma is *easier* than the full conjecture, and submitting it as a bare gap to Aristotle is more tractable.

---

## Sample prompt body

```
BRIDGE LEMMA SEARCH for the OPEN PROBLEM:

  {PROBLEM}

Your job is to factor {PROBLEM} into:

  {PROBLEM} = (KNOWN THEOREM A) + (KNOWN THEOREM B) + ... + (BRIDGE LEMMA L) + (PURELY FORMAL COMBINATION)

Where the BRIDGE LEMMA L is:
- A precisely statable proposition
- Currently unproven
- Strictly weaker than {PROBLEM}
- Combined with existing theorems (A, B, ...) and elementary manipulations, closes {PROBLEM}

For each candidate bridge lemma you propose (aim for 1-3):

### Candidate Bridge Lemma N

- **Lemma statement** (precise, with quantifiers and types — Lean-ish syntax welcome):
  ```
  lemma bridge_N (x : ...) (hx : ...) : ... := sorry
  ```

- **Existing theorems it composes with** (name + author + year + Mathlib location if known):
  - Theorem A: ...
  - Theorem B: ...

- **The gap between them**: state the exact reason A and B do not already imply {PROBLEM}. The gap is the bridge.

- **Compositional proof sketch** (3-5 lines, in English):
  Step 1: Apply Theorem A to obtain X.
  Step 2: Apply Bridge Lemma N to convert X to Y.
  Step 3: Apply Theorem B to Y to conclude {PROBLEM}.

- **Feasibility of proving Bridge Lemma N**: rate 1-5 where 1=trivial corollary, 5=as hard as {PROBLEM} itself.
  - If 1-2: WHY is the lemma so much easier? (Often: bounded, decidable, or a single residue class.)
  - If 3-5: Is there an iterated bridge (Lemma_M would imply Lemma_N)? If so, propose Lemma_M instead.

- **Is the bridge submittable as a bare gap to Aristotle?**: Yes/No. If Yes, draft the ≤30-line sketch headed `OPEN GAP: Bridge for {PROBLEM}`.

CONSTRAINTS:
- Avoid bridges that are "Schinzel's hypothesis H" or other conjectures of similar strength to {PROBLEM} itself. We want bridges that are genuinely smaller.
- Prefer bridges that are FINITE/COMPUTABLE in nature (bounded sets, residue classes, polynomial relations) because Aristotle excels on those.
- Be explicit about which steps are "elementary" — these should be Mathlib one-liners.

After listing your candidate bridges, recommend the SINGLE BEST bridge to attempt first. Justify in 2-3 sentences with explicit cost/yield reasoning.
```

---

## Wiring

```bash
python3 scripts/debate_fusion.py ${PROBLEM} --template bridge_lemma --rounds 2
mk debate ${PROBLEM} bridge_lemma
```
