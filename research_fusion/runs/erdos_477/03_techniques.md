# Erdős 477 — Stage 3 Named Techniques (W4-D, May 31 2026)

## Technique shortlist (ranked by fit for X^3 case)

### Primary (fit_score 0.45): Sekanina counting + centered-hexagonal mod-7 obstruction

**Named technique:** Sekanina-style finite modular obstruction transferred from X^2 to X^3 via the centered-hexagonal difference identity f(n+1)−f(n) = 3n²+3n+1.

**Justification:** This is the most natural extension of the only known closed case (X^2). Sekanina's argument is structurally:
1. Compute the difference operator Δf and show it enumerates a specific residue class.
2. Show that A inherits a modular density constraint from the bijection.
3. Use a mod-m argument (mod 4 in X^2) to derive contradiction.

For X^3, the obvious candidates for the mod-m obstruction are:
- **mod 7:** cubes mod 7 ∈ {0, 1, 6}, missing {2,3,4,5}. Centered hexagonals mod 7 ∈ {1, 5, 5, 2, 5, ...} cycle of length 7 hitting {1, 2, 4, 5}. The joint mod-7 structure of (a, n^3) pairs would force A to fill {2,3,4,5} (mod 7) exclusively from cubes-side gaps, contradicting uniqueness if the count overshoots.
- **mod 9:** cubes mod 9 ∈ {0, 1, 8}. Same template.
- **mod 13:** cubes mod 13 ∈ {0, 1, 5, 8, 12}. Five residues — also a natural candidate.

**Risk:** No published computation rules these out. Sekanina-style transfer is the cleanest path but may genuinely fail for cubic differences (which do not enumerate a residue class cleanly the way 2n+1 does for squares). Fit < 0.5 because cubic differences are SPARSER than odd numbers, weakening the residue-class argument.

### Secondary (fit_score 0.30): Newman polynomial-tiling generating-function unit

**Named technique:** Newman (1977) periodicity theorem applied via generating-function unit criterion in Z[[z,z^{-1}]].

**Justification:** The unique-representation condition Z = A ⊕ {n^3} is equivalent to a generating-function identity. Newman's tiling classification rules out certain prototile structures (those without cyclotomic factor support). Cubes have no cyclotomic structure in their generating function, so the unit criterion fails ⟹ no tiling exists.

**Risk:** Newman's theorem is for **finite** prototiles. The extension to infinite polynomial-image prototiles is NOT in the published literature; it would require deriving an analog ourselves. Fit 0.30 because the analog is plausible but unproven.

### Tertiary (fit_score 0.20): Plünnecke–Ruzsa sumset density refinement

**Named technique:** Sharpening of Pl–R sumset bound for unique-representation A ⊕ C = Z where |C ∩ [1,N]| ~ N^{1/3}.

**Justification:** Pl–R gives |A + A| ≪ |A|^{4/3} N^{1/3}. Uniqueness forces |A + A| ≥ (1−o(1)) · |A|^2. For |A| ~ N^{2/3}, both are N^{4/3} — borderline. A refinement that improves Pl–R by a log factor (or beats it by an additive-energy argument) might close.

**Risk:** Pl–R is borderline tight, not strict. The refinement does not exist in published literature. Fit 0.20 because the gap is logarithmic, not polynomial.

## Recommended primary technique

**Sekanina-style mod-7 (or mod-9, mod-13) finite modular obstruction transferred via the centered-hexagonal difference identity.**

This is what Aristotle's informal reasoner is best positioned to attempt because:
1. The X^2 proof template exists in Sekanina (1959) — a starting point.
2. The X^3 difference structure is COMPLETELY ELEMENTARY (Δf = 3n²+3n+1).
3. The modular search space is FINITE per modulus — Aristotle can enumerate (a, b, c) mod 7, mod 9, mod 13, mod 21, mod 63, ... and discover whether ANY modular argument closes the X^3 case.
4. If a modular argument exists, it will be a clean Lean 4 proof (finite case-check + density count).
5. If no modular argument exists, Aristotle will identify the residue class that fails — falsification is valid (E477 X^3 might be true but not provable by mod-m).

## Honest disclaimer

This dossier was assembled May 31 2026 by W4-D session (Claude Opus 4.7 1M-context) based on web search (Grok-4.3 May 30 first round + WebSearch May 31 second round) and the formal-conjectures repo. No paired-LLM consultation succeeded fully — Gemini quota was exhausted, Grok's "Ruzsa proved no exact complement of cubes" claim was HALLUCINATED (verified against arXiv:1510.00812 abstract, which makes no such claim). The Sekanina-style transfer is the AUTHOR'S analysis, not a paired-LLM-validated strategy. fit_score 0.45 for the primary technique reflects HONESTY: the mod-m argument may or may not close; the search space is finite but the obstruction is unknown.

## arXiv seminal paper

There is NO arXiv paper specific to E477 X^3. The closest seminal paper for the proof template is **Sekanina (1959)** itself (Czechoslovak Math J 9:485–495, http://dml.cz/dmlcz/100376), which is pre-arXiv. We list `"seminal_paper_arxiv": "none"` in the companion.
