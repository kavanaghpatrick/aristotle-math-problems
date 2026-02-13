# Erdős Problem 1064: Assessment for INFORMAL Submission

## Problem Statement

**Theorem**: The set {n : φ(n) > φ(n - φ(n))} has asymptotic density 1.

Where φ is Euler's totient function and n - φ(n) is the cototient.

**Status**: PROVED by Luca and Pomerance (2002), published in *Colloquium Mathematicum* Vol. 92, pp. 111-130.

## Known Results (from erdosproblems.com/1064)

1. **Density 1 (Main Result)**: Luca & Pomerance proved the set has density 1
2. **Stronger Result**: For any f(n) = o(n), φ(n) > φ(n - φ(n)) + f(n) holds for almost all n
3. **Infinitely Many Counterexamples**: φ(n) < φ(n - φ(n)) for infinitely many n
   - Example: n = 15·2^k gives φ(n) = 4·2^k and φ(n - φ(n)) = 5·2^k
4. **Equality Cases**: φ(n) = φ(n - φ(n)) for infinitely many n
   - Example: n = 3·2^k for k ≥ 1 (OEIS A051487)
5. **Lower Bound**: Grytczuk, Luca, Wójtowicz (2001) proved lower density ≥ 0.54
6. **Constant Factor**: φ(n) < c·φ(n - φ(n)) for infinitely many n, any c > 0

## Proof Outline (Reconstructed from Research)

### Key Observation

For most n, the cototient n - φ(n) is significantly smaller than n, so:
- φ(n) ≈ n · ∏(1 - 1/p) where p | n
- n - φ(n) ≪ n for typical n
- φ(n - φ(n)) ≈ (n - φ(n)) · (similar product)
- Since n - φ(n) ≪ n, we expect φ(n) > φ(n - φ(n))

### Likely Proof Strategy

1. **Smooth Number Analysis**: Numbers with many small prime factors have large φ(n)/n ratio
   - For smooth n, φ(n) is relatively large compared to n
   - n - φ(n) is small
   - Therefore φ(n - φ(n)) is even smaller

2. **Asymptotic Density Arguments**:
   - Show the "good" set (where inequality holds) has positive lower density
   - Show the complement has density 0
   - Uses techniques from probabilistic number theory (Hardy-Ramanujan style)

3. **Exceptional Set Analysis**:
   - Counterexamples like n = 15·2^k have special structure
   - These form a set of density 0 (geometric progressions have density 0)
   - Equality cases also have density 0

### Technical Tools (Based on Luca-Pomerance Style)

From their 2020 paper "Phi, Primorials, and Poisson":
- Normal order analysis (typical behavior vs exceptional)
- Asymptotic density via counting arguments
- Poisson distribution limits for rare events
- Primorial divisibility analysis

## Suitability Assessment for INFORMAL Sketch

### DIFFICULTY: **MODERATE-HIGH**

**Challenges**:

1. **Analytic Techniques**: The proof uses asymptotic density arguments, which require:
   - Understanding of natural density (HasDensity in Lean)
   - Asymptotic analysis (Big-O notation, limiting behavior)
   - Probabilistic number theory methods

2. **Mathlib Support**:
   - ✅ Euler's totient: `Nat.totient` exists
   - ✅ HasDensity: exists in Mathlib4 (natural density)
   - ⚠️  Asymptotic analysis: partial support
   - ❓ Normal order: likely needs development

3. **Proof Length**: Original paper is ~20 pages for multiple results
   - This specific result is probably 5-10 pages
   - Requires technical lemmas about smooth numbers, density estimates

4. **Domain**: Number Theory ✅ (75-97% AI success rate)

### FEASIBILITY: **BORDERLINE**

**Against INFORMAL submission**:
- Proof requires sophisticated analytic NT (density arguments)
- May need multiple auxiliary lemmas about asymptotic behavior
- Paper is 20+ pages, unclear how much is needed for this specific result
- We don't have the actual proof text, only bibliographic references

**For INFORMAL submission**:
- NT domain has high success rate (75-97%)
- Result is PROVED, not open research
- Statement is clean and well-defined
- HasDensity exists in Mathlib
- We can write a high-level sketch even without full proof details

## Recommendation

### PRIMARY RECOMMENDATION: **DEFER UNTIL PROOF ACCESS**

This problem is **conditionally suitable** for INFORMAL:

1. **If we can access the Luca-Pomerance paper**:
   - Read the proof
   - Write 80-line sketch capturing main argument
   - Submit as INFORMAL with Track A

2. **If we cannot access the paper**:
   - **Do NOT attempt** — sketching without proof knowledge is low-quality
   - The proof techniques matter for this result
   - Guessing the argument could lead to failed submission

### ALTERNATIVE: Screen for Simpler Totient Problems

The research revealed:
- **Lehmer totient problem** (already in our DB)
- Totient iteration problems
- Composition problems φ(σ(n)), σ(φ(n))

These might have more accessible proofs.

## Next Steps if Pursuing

1. **Access the paper**:
   - DOI: 10.4064/cm92-1-10
   - MR: 1899242
   - Try library access or request from authors

2. **Study the proof**:
   - Identify main lemmas
   - Map proof structure
   - Check Mathlib for needed infrastructure

3. **Write sketch**:
   - 80-100 lines
   - Include: statement, main lemmas, asymptotic argument, exceptional set analysis
   - Reference specific Mathlib lemmas where possible

4. **Submit as INFORMAL**:
   - Track A workflow
   - NT domain (favorable)
   - First-ever formalization (high novelty value)

## References

- Erdős Problem 1064: https://www.erdosproblems.com/1064
- F. Luca, C. Pomerance, "On some problems of Mąkowski-Schinzel and Erdős concerning the arithmetical functions φ and σ", *Colloq. Math.* 92 (2002), 111-130
- A. Grytczuk, F. Luca, M. Wójtowicz, *Publ. Math. Debrecen* 59 (2001), 9-16
- OEIS A051487: Numbers n such that φ(n) = φ(n - φ(n))

## Conclusion

This is a **high-value target** (first-ever formalization, NT domain, proven result) but requires **proof access** before attempting. Without the actual proof, we cannot write a quality sketch that would give Aristotle sufficient guidance in INFORMAL mode.

**Status**: HOLD pending paper access.
