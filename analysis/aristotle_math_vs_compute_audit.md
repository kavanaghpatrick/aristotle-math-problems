# Aristotle: Mathematical Reasoning vs Computational Brute Force — Audit F1

**Date:** 2026-05-30
**Auditor:** Agent F1 (HONEST AUDIT, 10-agent fleet)
**Scope:** Every `compiled_advance` artifact + the slot740 disproof.

## Rubric

| Category | Definition |
|---|---|
| **PURE COMPUTE** | Theorem body is a single bounded `native_decide` / `decide`. No mathematical content from Aristotle. |
| **COMPUTE + LIGHT GLUE** | `interval_cases` / case-split / sub-list checks + `native_decide`. Mathematical framing is in the *sketch*, Aristotle just wires the kernel. |
| **STRUCTURAL REASONING** | Aristotle introduced a non-obvious lemma, decomposition, or case-split — real math, where compute appears only at deep leaves. |
| **CROSS-DOMAIN FUSION** | Aristotle imported a technique from a different mathematical area to solve the problem (the user's actual goal). |

## Per-Advance Categorization

### slot720_iter2 — Feit-Thompson p=3, q≡71 (mod 72), q≤1000

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot720_iter2_ft_family_result.lean` (87 lines, 9× `native_decide`)

**Category:** **STRUCTURAL REASONING** (mild)

**Evidence:**
- Aristotle introduced `not_dvd_via_fermat_factor`: a structural lemma stating "if p|A(q) and 3^(q mod (p-1)) ≢ 1 mod p, then ¬ (q²+q+1) ∣ (3^q-1)/2." The proof uses Fermat's Little Theorem to rewrite 3^q ≡ 3^(q%(p-1)) (mod p).
- For each of 7 primes in the family {71, 359, 431, 503, 647, 719, 863} Aristotle SELECTED a specific small prime divisor p of q²+q+1 (e.g. for q=359 it picked p=7; for q=647 it picked p=211). These selections are NOT in the sketch.
- The selection avoided the computational explosion that would occur from `native_decide` on 3^863.
- Lemma+selection are genuine mathematical work. The "leaf" verifications (decide that p∣A(q), native_decide that 3^k%p≠1) are pure compute, but the surrounding scaffold is math.

**However:** still inherently small-scale; the math is "Fermat reduction → pick a prime → compute" — a known technique applied mechanically.

---

### slot722_iter2 — Brocard's conjecture for n ∈ [2, 500]

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot722_iter2_brocard_extended_result.lean` (67 lines, 4× `native_decide`)

**Category:** **COMPUTE + LIGHT GLUE** (with one piece of useful engineering)

**Evidence:**
- The actual mathematical content is the `nthPrimeComp` definition (computable n-th prime via `Nat.find`) and its bridge to noncomputable `Nat.nth Nat.Prime` via `Nat.nth_count`. This IS a piece of nontrivial Lean engineering — but it's a Mathlib-adjacent transcription, not a mathematical advance.
- The actual Brocard inequality verification is `by native_decide` over `Finset.Icc 2 500`.
- The "structural" framing claimed in the DB (`STRUCTURAL PROOF...parametrized by N and scales by changing one constant`) is honest about iter2 vs iter1 (50 manual lemmas), but the proof is still fundamentally a brute-force interval check wrapped in a computability bridge.

---

### slot736 — Feit-Thompson p=3, q≡71 (mod 72), q≤1500

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot736_extracted/.../Main.lean` (22 lines, 1× `native_decide`)

**Category:** **PURE COMPUTE**

**Evidence (full proof body, 4 lines):**
```lean
  suffices h : ∀ q ∈ Finset.range 1501, q.Prime → 3 < q → q ≡ 71 [MOD 72] →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 by
    intro q hq1 hq2 hq3 hq4
    exact h q (Finset.mem_range.mpr (by omega)) hq1 hq2 hq3
  native_decide
```

Aristotle reduced the universal quantifier to `Finset.range 1501` and discharged ALL 11 primes (including q=1439, where 3^1439 is astronomical) with a single `native_decide`. **The proof contains zero mathematical insight.** It's a regression vs slot720_iter2 (which used Fermat reduction). Slot720_iter2 picked the structural path; slot736 chose brute force and the heartbeats budget happened to fit.

---

### slot737 — Erdős 647 Sophie subclass

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot737_extracted/.../Erdos647.lean` (168 lines, **0× `native_decide`**)

**Category:** **STRUCTURAL REASONING** (the strongest example)

**Evidence:**
- Helper `sigma0_three_mul_composite_ge6`: For composite c ≥ 999, σ₀(3c) ≥ 6. Aristotle decomposed c = 3^a · m, used **multiplicativity of σ₀** (`ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime`), case-split on a=0 vs m=1 vs both nonzero.
- Helper `sigma0_four_mul_composite_ge7`: Analogous for σ₀(4d) ≥ 7 via d = 2^a · m.
- Helper `Nat.card_divisors_composite`: Composite n>1 has ≥3 divisors via `Finset.two_lt_card_iff`.
- The 12|n derivation from `(n-2)/2 prime` + `Nat.Prime.eq_two_or_odd` + omega.
- Final witness construction: chooses m=n-3 or m=n-4 based on the `hsplit` disjunction.

This is **actual number-theoretic reasoning**. The sketch supplied the framing (3000 ≤ n, 6|n, n-1 prime, q prime, hsplit) but did NOT mention multiplicativity, divisor decomposition, or the m=n-3 / m=n-4 witness choice. Aristotle introduced those.

**Zero `native_decide` calls anywhere in the proof.**

---

### slot738 — Brocard's conjecture for n ∈ [501, 1000]

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot738_extracted/.../Main.lean` (751 lines, 11× `native_decide`)

**Category:** **COMPUTE + LIGHT GLUE** (but with an ALARMING external dependency)

**Evidence:**
- The summary explicitly states: "I computed (via a verified Python sieve up to p₁₀₀₁² ≈ 63 million) four explicit prime witnesses lying strictly between p_n² and p_{n+1}²".
- **The 2000 witness primes were generated OUTSIDE Lean by a Python sieve. They are hardcoded into the 10 data chunks.** Aristotle wrote a Bool-valued checker `checkEntryB` and discharged each chunk's correctness via `native_decide`.
- The structural part — `four_le_card_filter_of_witnesses` (subset cardinality), `nth_prime_of_count` (bridging) — is competent but standard Lean engineering.
- This is the **same** pattern as slot722_iter2 scaled up: precompute the answer externally, then verify in Lean. The Lean proof contributes essentially zero new mathematics.

---

### slot739 — Leinster nonabelian group D₃ × C₅

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot739_extracted/.../Main.lean` (349 lines, 2× `native_decide`, both at deep leaves)

**Category:** **STRUCTURAL REASONING** (the second-strongest example)

**Evidence:**
- `fst_one_mem_of_mem_coprime`: For G×H with gcd(|G|,|H|)=1, if (g,h) ∈ K then (g,1) ∈ K. **Proof uses Bezout** to construct integers a,b with a|H|+b·ord(g)=1, then derives (g^|H|, 1) ∈ K via `K.pow_mem`, lifts to integer powers via `K.zpow_mem`, uses `pow_orderOf_eq_one`. This is genuine group-theoretic reasoning.
- `normal_subgroup_of_coprime_prod`: Every normal subgroup of coprime G×H is a product. Direct consequence of the Bezout lemma.
- `DihedralGroup.normal_with_sr_eq_top`: Normal subgroup containing a reflection contains all reflections via conjugation (fin_cases on ZMod 3), then all rotations via multiplication.
- `DihedralGroup.le_rot_eq_bot_or_rot`: Subgroup of order-3 subgroup divides 3 (Lagrange), prime case-split.
- The classification of normal subgroups of D₃ {⊥, rotations, ⊤} is derived from the above, not asserted.
- `normalSubgroupOrderSum_prod_coprime`: σ(G×H) = σ(G)·σ(H) via `Finset.sum_bij` over normal subgroup pairs, then `Finset.sum_product` and `Finset.mul_sum`.
- Final assembly: σ(D₃)=10, σ(C₅)=6, hence σ(D₃×C₅)=60=2·30. The `native_decide` calls are ONLY for `Nat.Coprime 6 5` and "is D₃×C₅ nonabelian".

This is the cleanest example of Aristotle doing real mathematics. The sketch said "S₃ × C₅ is a Leinster group" with no proof guidance. Aristotle:
1. Switched the witness from `S₃` (=`Equiv.Perm (Fin 3)`) to `DihedralGroup 3` (isomorphic but more tractable in Mathlib).
2. Derived multiplicativity of σ for coprime products via Bezout (this is the substantive lemma).
3. Classified normal subgroups of D₃ via conjugation arguments.

---

### slot740 — Erdős 203 index-1 covering disproof

**File:** `/Users/patrickkavanagh/math/submissions/nu4_final/slot740_extracted/.../Main.lean` (55 lines, 1× `native_decide`)

**Category:** **STRUCTURAL REASONING (in plan) + PURE COMPUTE (in Lean)**

**Evidence:**
- The sketch claimed the theorem `index1_covering_insufficient_M8_B500` was OPEN and conjectured TRUE.
- Aristotle **disproved it** by exhibiting `m = 1579554969991861182625270235031094424159694` and showing every (k,l) ∈ [0,8)² is caught by some index-1 prime p ≤ 500.
- The summary describes the construction: (1) partition [0,8)² by each prime's class, (2) greedy set cover over 25 multi-cell primes finds 22 primes covering all 64 cells, (3) Chinese Remainder Theorem reconstructs a single m realizing the cover.
- **This greedy-set-cover-then-CRT analysis is mathematically real and Aristotle did it.** It's not in the sketch.
- **However:** the analysis was done EXTERNALLY (not in Lean). The Lean proof itself is `⟨counterexample_m, by native_decide⟩` — pure compute verifying a precomputed witness.

The math is real. The Lean is brute force. The external work is invisible to our pipeline — we have no audit trail of the greedy/CRT computation.

## Aggregate Breakdown

| # | Slot | Problem | Category | Notes |
|---|---|---|---|---|
| 1 | 720 | FT family q≤1000 | STRUCTURAL (mild) | Fermat reduction, manual prime selection per q |
| 2 | 722 | Brocard [2,500] | COMPUTE + GLUE | Computability bridge + `native_decide` |
| 3 | 736 | FT family q≤1500 | **PURE COMPUTE** | One `native_decide` — regression from slot720 |
| 4 | 737 | Erdős 647 Sophie | **STRUCTURAL** | σ₀ multiplicativity, divisor decomp, **0 `native_decide`** |
| 5 | 738 | Brocard [501,1000] | COMPUTE + GLUE | 2000 witnesses from Python sieve, not Aristotle |
| 6 | 739 | Leinster D₃×C₅ | **STRUCTURAL** | Bezout, normal subgroup classification, σ multiplicativity |
| 7 | 740 | Erdős 203 disproof | STRUCTURAL (external) + COMPUTE (Lean) | Greedy/CRT done outside Lean, witness verified by `native_decide` |

**Counts:**
- PURE COMPUTE: 1 (slot736)
- COMPUTE + LIGHT GLUE: 2 (slot722, slot738) — *both Brocard, both same recipe*
- STRUCTURAL REASONING: 3 (slot720 mild, slot737, slot739)
- STRUCTURAL+COMPUTE HYBRID: 1 (slot740 — math outside Lean, verify in Lean)
- **CROSS-DOMAIN FUSION: 0**

**Aggregate verdict:** Approximately **3 of 7 advances (43%) involve real mathematical structure.** 4 of 7 are dominated by brute-force `native_decide` or external precomputation. **Zero of seven** show Aristotle applying a technique from a genuinely different field to solve a problem in another.

The "structural" wins are also constrained to *standard techniques in the obvious field*:
- slot720/736: Fermat's little theorem (number theory → number theory).
- slot737: σ multiplicativity (number theory → number theory).
- slot739: Bezout + Sylow-flavored arguments (group theory → group theory).
- slot740: greedy set cover + CRT (combinatorics + number theory, mildly cross-domain at best).

## Best Mathematical Output

**slot739 (Leinster D₃ × C₅).** Aristotle proved σ multiplicativity for coprime finite groups via a clean Bezout argument:

```
If (g,h) ∈ K and gcd(|G|,|H|)=1, then (g^|H|, 1) ∈ K, and
g ∈ ⟨g^|H|⟩ via a·|H| + b·ord(g) = 1, hence (g, 1) ∈ K.
```

The proof is 349 lines, **only 2 `native_decide`** calls (both at trivial leaves: "are 6 and 5 coprime?", "is D₃×C₅ nonabelian?"). Every non-trivial step is real algebra: `K.pow_mem`, `K.zpow_mem`, `pow_orderOf_eq_one`, `Subgroup.Normal.map`, `Finset.sum_bij`. The witness substitution S₃ → DihedralGroup 3 was Aristotle's choice, not the sketch's.

## Worst Brute-Force Output

**slot736 (FT q≤1500).** The entire proof:

```lean
theorem feit_thompson_p3_q71_family_1500 :
    ∀ q : ℕ, q.Prime → 3 < q → q ≡ 71 [MOD 72] → q ≤ 1500 →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  suffices h : ∀ q ∈ Finset.range 1501, q.Prime → 3 < q → q ≡ 71 [MOD 72] →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 by
    intro q hq1 hq2 hq3 hq4
    exact h q (Finset.mem_range.mpr (by omega)) hq1 hq2 hq3
  native_decide
```

This is the SAME problem family as slot720_iter2, where Aristotle previously did the (mild) Fermat reduction. In slot736, given a higher bound (1500), Aristotle abandoned the structural approach and brute-forced 3^1439 via `native_decide`. It compiled. We celebrated it as `compiled_advance`. The DB says `target_resolved=0`, so this isn't dishonest, but it shows that **when given the choice, Aristotle defaults to compute.**

## Evidence of Cross-Domain Reasoning

**None.** No advance has Aristotle reaching into a non-obvious field. Every "structural" advance uses techniques native to the problem's own area. The closest is slot740 (greedy set cover applied to a number-theoretic covering problem) — but covering systems and CRT are the canonical tools for Erdős-203-style problems, so this is in-domain.

## What Would Need to Change for Real Math

1. **Stop counting `native_decide`-dominant proofs as advances.** slot736 should be `compiled_no_advance`. The DB schema allows this (`target_resolved=0`) but the success label inflates the perceived hit rate. Of 7 "advances," only 3 (737, 739, the planning side of 740) are advances in the math-not-compute sense.

2. **Refuse Python-precomputed witnesses.** slot738 imported 2000 primes from a Python sieve and verified them in Lean. The Lean proof is honest, but the *mathematical work* (finding witnesses) was done in numpy. If we want Aristotle to do math, the witness search must happen inside the reasoning loop.

3. **Reward cross-domain attempts.** Currently 0 of 7 advances use technique from outside the problem's home field. Sketches like "find a Lehmer counterexample via elliptic-curve heights" or "attack union-closed via spectral graph theory" are not in our recent pipeline. Submitting problems with explicit cross-domain hints in *adjacent* slots (so context fuses) might encourage transfer. (Right now we attach context from prior attempts on the *same* problem.)

4. **Stop celebrating bounded verification as "closure."** slot722/736/738 verify bounded instances of unbounded conjectures. They are tabulations, not theorems. The contribution_statement field says this honestly. The success label does not.

5. **Track external compute.** slot740's greedy+CRT, slot738's Python sieve — these are real work but invisible to math-forge. We currently can't distinguish "Aristotle thought" from "Aristotle delegated to Python." That's the audit gap.
