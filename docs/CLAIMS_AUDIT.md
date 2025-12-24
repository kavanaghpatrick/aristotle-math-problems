# Project Claims Audit - December 2024

## Executive Summary

After thorough investigation, several claims in this project are **misleading or inaccurate**. This document catalogues all issues and proposed fixes.

---

## 1. File Naming Issues

### Files Named "*_SUCCESS.lean" - Misleading

| File | What It Claims | What It Actually Proves | Proposed Rename |
|------|---------------|------------------------|-----------------|
| `erdos153_v4_SUCCESS.lean` | Erdős #153 solved | Sidon set bounds (known math) | `erdos153_sidon_bounds.lean` |
| `erdos_turan_sidon_bound_SUCCESS.lean` | Same file | Duplicate | DELETE (duplicate) |
| `erdos190_SUCCESS.lean` | Erdős #190 solved | Lower bound technique | `erdos190_lower_bound_technique.lean` |
| `erdos593_SUCCESS.lean` | Erdős #593 solved | Incidence graph bipartite | `erdos593_bipartite_lemma.lean` |
| `erdos1052_SUCCESS_even.lean` | Erdős #1052 solved | "Unitary perfect are even" | `erdos1052_even_proved.lean` (VALID!) |
| `tuza_SUCCESS_nu1_case.lean` | Tuza solved | ν=1 case proved | `tuza_nu1_case_proved.lean` (VALID!) |
| `tuza_iteration3_alt_SUCCESS.lean` | Tuza solved | ν=1 case alternate proof | `tuza_nu1_alt_proof.lean` |
| `tuza_SUCCESS_conditional.lean` | Tuza solved | IF reduction THEN Tuza | `tuza_conditional_proof.lean` |

### Actually Valid "Proven" Claims:
- **erdos1052_SUCCESS_even.lean**: Actually proves "all unitary perfect numbers are even" - REAL RESULT
- **tuza_SUCCESS_nu1_case.lean**: Actually proves τ≤2 when ν=1 - REAL RESULT (part of Parker's proof)

---

## 2. Database Issues

### Contradictory Entries in literature_lemmas

| Lemma | proof_status | axiom_confidence | Issue |
|-------|-------------|------------------|-------|
| `k4_cover` | proven | should_prove | **Contradictory** - if proven, shouldn't need proving |
| `tau_union_le_4_v_decomp` | refuted | peer_reviewed | Honest - lemma was invalidated |
| `parker2024_nu_le_3` | gap | N/A | Honest - acknowledges gap |
| `bridge_count_limit` | depends_on_sorry | N/A | Honest |

### Overstated novelty_level Claims

Many submissions marked "discovery" are actually:
- Formalizations of known results
- Extensions of existing proofs
- Helper lemmas

---

## 3. proven/ Directory Issues

### File with sorry in proven/
- **`proven/tuza/lemmas/parker_lemmas.lean`** has `sorry` at line 579
- Should be moved to `submissions/` until complete

### Budget-Exhausted Files
Several files in proven/ say "Aristotle's budget has been reached" - need verification:
- `proven/tuza/nu0/tuza_nu0_PROVEN.lean`
- `proven/tuza/nu1/tuza_nu1_PROVEN.lean`

---

## 4. README Claims (FIXED)

The README was updated on 2024-12-23 to be more honest:
- Changed "Erdős Problems (Fully Proven)" to "Related Work"
- Changed "Proven" to "Formalized" for Tuza ν≤3 cases
- Removed "Erdős problems solved | 3" statistic

---

## 5. Honest Assessment

### What We Actually Have:

**Genuine Contributions (if ν=4 succeeds):**
- 87 proven lemmas for scaffolding
- ν=4 attack infrastructure

**Formalizations (valuable but not discoveries):**
- Tuza ν≤3 (Parker 2024 proof)
- Various Sidon set bounds
- Incidence graph properties

**Open Targets (genuinely open):**
- **ν=4 case** - This is where real discovery could happen
- Split graphs (general case)
- Counterexample search

### Key Insight

The project's value is in **building infrastructure for genuinely open problems**, not in claiming to have solved them. The honest path forward is:

1. Fix misleading file names
2. Update database entries
3. Focus claims on what's genuinely proven vs. formalized
4. Continue attacking ν=4 (the real open problem)

---

## Action Items

- [ ] Rename SUCCESS files to accurate names
- [ ] Move parker_lemmas.lean out of proven/ (has sorry)
- [ ] Fix contradictory database entries
- [ ] Review all novelty_level = 'discovery' claims
- [ ] Verify files in proven/ are actually complete
