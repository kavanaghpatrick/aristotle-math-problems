#!/usr/bin/env python3
"""
Create GitHub Issues for All Aristotle Math Problems
Generates 50+ issues organized by tier, category, and difficulty
"""

import subprocess
import json
import time

# Issue template
ISSUE_TEMPLATE = """## Problem Statement

{statement}

## Why Tractable for Aristotle

{why_tractable}

## Metadata

- **Success Probability**: {success_rate}%
- **Estimated Time**: {time_estimate}
- **Difficulty**: {difficulty}
- **Impact**: {impact}
- **Mathlib Support**: {mathlib_support}

## Aristotle Command

```bash
# Create problem file
cat > {filename} << 'EOF'
{problem_text}
EOF

# Run Aristotle
aristotle prove-from-file --informal {filename}
```

## Expected Outcome

{expected_outcome}

## References

{references}

---

*Part of the Aristotle Math Problems project. Generated from comprehensive AI research across Grok, Gemini, and Claude agents.*
"""

# All problems organized by tier
PROBLEMS = {
    "TIER_1": [
        {
            "title": "Goldbach Conjecture for n ≤ 10^6",
            "statement": "Prove that every even integer n where 4 ≤ n ≤ 1,000,000 can be expressed as the sum of two prime numbers.",
            "why_tractable": "- Finite verification problem with clear bounds\n- Mathlib has strong prime number infrastructure\n- Computational verification to 4×10^18 already done\n- Direct algorithmic approach: iterate + primality test",
            "success_rate": 85,
            "time_estimate": "1 week",
            "difficulty": "IMO Problem 3-4 level",
            "impact": "HIGH - Partial result on famous unsolved problem",
            "mathlib_support": "Good (prime theory)",
            "category": "number-theory",
            "filename": "goldbach_bounded.txt",
            "problem_text": "Prove that every even integer n where 4 ≤ n ≤ 1000000 can be expressed as the sum of two prime numbers.",
            "expected_outcome": "Formal verification of bounded Goldbach conjecture. Publishable result even if bounded. Potential Mathlib contribution.",
            "references": "- [Goldbach's conjecture - Wikipedia](https://en.wikipedia.org/wiki/Goldbach's_conjecture)\n- Verified computationally to 4×10^18",
            "type": "open-problem"
        },
        {
            "title": "Sum of Two Squares Characterization",
            "statement": "Prove that a positive integer n is expressible as the sum of two squares (n = a² + b²) if and only if in its prime factorization, every prime of the form 4k+3 appears to an even power.",
            "why_tractable": "- Classical theorem with known elementary proof\n- Likely partially formalized in Mathlib\n- Pure modular arithmetic, no advanced techniques needed\n- Clear algorithmic structure",
            "success_rate": 95,
            "time_estimate": "3-5 days",
            "difficulty": "IMO Problem 2-3 level",
            "impact": "MEDIUM - Classical theorem formalization, Mathlib contribution",
            "mathlib_support": "Excellent (modular arithmetic)",
            "category": "number-theory",
            "filename": "sum_of_two_squares.txt",
            "problem_text": "Prove that a positive integer n can be expressed as n = a² + b² for some integers a and b if and only if in the prime factorization of n, every prime congruent to 3 modulo 4 appears to an even power.",
            "expected_outcome": "Complete formalization of Fermat's theorem on sums of two squares. Major Mathlib contribution to number theory.",
            "references": "- [Fermat's theorem on sums of two squares - Wikipedia](https://en.wikipedia.org/wiki/Fermat's_theorem_on_sums_of_two_squares)\n- Elementary proof via Gaussian integers",
            "type": "formalization"
        },
        {
            "title": "McKay Conjecture Formalization",
            "statement": "Formalize the McKay conjecture in Lean 4: For a finite group G and prime p, the number of irreducible characters of G with degree not divisible by p equals the same number for the normalizer of a Sylow p-subgroup.",
            "why_tractable": "- Recently proven by Späth and Cabanes (2023)\n- Verification task, not discovery\n- Well-defined finite group theory\n- Advances Lean 4 group theory infrastructure",
            "success_rate": 75,
            "time_estimate": "3 weeks",
            "difficulty": "Research level formalization",
            "impact": "HIGH - Major research-level formalization",
            "mathlib_support": "Medium (group theory)",
            "category": "algebra",
            "filename": "mckay_conjecture.txt",
            "problem_text": "Formalize the McKay conjecture: For a finite group G and prime p, prove that the number of irreducible characters of G with degree not divisible by p equals the number of irreducible characters of N_G(P) with degree not divisible by p, where P is a Sylow p-subgroup of G.",
            "expected_outcome": "Complete formalization of recently proven theorem. Major contribution to Mathlib group theory. Potential publication.",
            "references": "- [McKay conjecture - Wikipedia](https://en.wikipedia.org/wiki/McKay_conjecture)\n- Proven by Späth & Cabanes (2023)",
            "type": "formalization"
        },
        {
            "title": "Fermat Number F₅ Compositeness",
            "statement": "Prove that the fifth Fermat number F₅ = 2^32 + 1 is composite by exhibiting its complete factorization: F₅ = 641 × 6700417.",
            "why_tractable": "- Elementary verification by multiplication\n- Known factorization exists\n- Simple arithmetic operations only\n- Good test of basic capabilities",
            "success_rate": 98,
            "time_estimate": "1-2 days",
            "difficulty": "IMO Problem 1-2 level",
            "impact": "LOW - Simple verification, good confidence builder",
            "mathlib_support": "Good (basic arithmetic)",
            "category": "number-theory",
            "filename": "fermat_f5.txt",
            "problem_text": "Prove that F₅ = 2^32 + 1 is composite by showing that F₅ = 641 × 6700417.",
            "expected_outcome": "Quick verification success. Validates Aristotle setup and basic arithmetic handling.",
            "references": "- [Fermat number - Wikipedia](https://en.wikipedia.org/wiki/Fermat_number)\n- Factorization discovered by Euler",
            "type": "formalization"
        },
        {
            "title": "Lagrange's Four-Square Theorem",
            "statement": "Prove that every positive integer can be expressed as the sum of at most four perfect squares. Additionally, characterize which numbers require exactly four squares (those of the form 4^a(8b+7)).",
            "why_tractable": "- Classical theorem proven in 1770\n- Elementary proof exists\n- Clear modular arithmetic structure\n- Well-studied problem",
            "success_rate": 80,
            "time_estimate": "1 week",
            "difficulty": "IMO Problem 3-4 level",
            "impact": "MEDIUM - Classical theorem, good formalization exercise",
            "mathlib_support": "Good (modular arithmetic)",
            "category": "number-theory",
            "filename": "four_square_theorem.txt",
            "problem_text": "Prove Lagrange's Four-Square Theorem: Every positive integer can be expressed as the sum of at most four perfect squares. Also characterize which numbers require exactly four squares.",
            "expected_outcome": "Complete formalization of classical theorem. Potential Mathlib contribution to additive number theory.",
            "references": "- [Lagrange's four-square theorem - Wikipedia](https://en.wikipedia.org/wiki/Lagrange's_four-square_theorem)\n- [Waring's problem - Wikipedia](https://en.wikipedia.org/wiki/Waring's_problem)",
            "type": "formalization"
        },
        {
            "title": "IMO Cyclic Inequality (A5/A6 Level)",
            "statement": "For positive real numbers a, b, c, prove that:\na³/(b²+c²) + b³/(c²+a²) + c³/(a²+b²) ≥ (a+b+c)/2",
            "why_tractable": "- IMO Problem 6 difficulty level\n- Multiple proof strategies: Cauchy-Schwarz, substitution, AM-GM chains\n- Tests Aristotle's inequality handling\n- Known to be true with sophisticated proof",
            "success_rate": 60,
            "time_estimate": "1 week",
            "difficulty": "IMO Problem 5-6 level",
            "impact": "MEDIUM - Validates capabilities on hardest olympiad problems",
            "mathlib_support": "Good (inequality theory)",
            "category": "analysis",
            "filename": "imo_cyclic_inequality.txt",
            "problem_text": "For positive real numbers a, b, c, prove that:\n(a³/(b²+c²)) + (b³/(c²+a²)) + (c³/(a²+b²)) ≥ (a+b+c)/2",
            "expected_outcome": "Successful proof validates IMO gold medal capability. Demonstrates advanced inequality techniques.",
            "references": "- IMO shortlist A5/A6 difficulty\n- [Olympiad Inequalities - Thomas Mildorf](https://artofproblemsolving.com/articles/files/MildorfInequalities.pdf)",
            "type": "open-problem"
        },
        {
            "title": "Linear Diophantine Equations (General Algorithm)",
            "statement": "For given integers a, b, c, implement and verify a complete algorithm to find all integer solutions to ax + by = c, or prove that no solutions exist.",
            "why_tractable": "- Completely solved problem (Extended Euclidean Algorithm)\n- Polynomial-time decidable\n- Constructive proof exists\n- Already formalized in Isabelle/HOL",
            "success_rate": 99,
            "time_estimate": "1-2 days",
            "difficulty": "IMO Problem 1 level",
            "impact": "MEDIUM - Fundamental algorithm, excellent Mathlib contribution",
            "mathlib_support": "Excellent (GCD, Bezout)",
            "category": "number-theory",
            "filename": "linear_diophantine.txt",
            "problem_text": "For integers a, b, c, find all integer solutions (x, y) to the equation ax + by = c. Prove the algorithm is complete and correct.",
            "expected_outcome": "Complete verified implementation of Extended Euclidean Algorithm. Fundamental Mathlib contribution.",
            "references": "- [Diophantine equation - Wikipedia](https://en.wikipedia.org/wiki/Diophantine_equation)\n- [Formally Verified Solver (Isabelle)](https://link.springer.com/chapter/10.1007/978-3-319-94821-8_26)",
            "type": "formalization"
        },
        {
            "title": "Fortune's Conjecture for n ≤ 1000",
            "statement": "For all n ≤ 1000, verify that the Fortunate number m_n (the smallest integer m > 1 such that primorial p_n# + m is prime) is itself prime.",
            "why_tractable": "- Finite verification problem\n- Verified computationally to n=3000\n- Clear algorithmic structure: compute primorial, search for next prime\n- Elementary number theory only",
            "success_rate": 75,
            "time_estimate": "3-5 days",
            "difficulty": "IMO Problem 3 level",
            "impact": "MEDIUM - Bounded verification of interesting conjecture",
            "mathlib_support": "Good (primes, factorials)",
            "category": "number-theory",
            "filename": "fortune_conjecture.txt",
            "problem_text": "For all n ≤ 1000, prove that the Fortunate number m_n (smallest m > 1 where p_n# + m is prime, where p_n# is the n-th primorial) is itself prime.",
            "expected_outcome": "Verification of Fortune's conjecture for bounded cases. Demonstrates computational + proof capabilities.",
            "references": "- [Fortunate number - Wikipedia](https://en.wikipedia.org/wiki/Fortunate_number)\n- Verified to n=3000",
            "type": "open-problem"
        },
    ],
    "TIER_2": [
        {
            "title": "Anderson-Badawi Conjecture (n=3)",
            "statement": "Prove that every 3-absorbing ideal of a commutative ring is strongly 3-absorbing.",
            "why_tractable": "- Proven for n=2, natural next case\n- Pure algebra, well-defined ideal operations\n- Specific case of broader conjecture\n- Elementary ring theory",
            "success_rate": 50,
            "time_estimate": "3 weeks",
            "difficulty": "Research level",
            "impact": "HIGH - Potential breakthrough on open problem",
            "mathlib_support": "Medium (ring theory)",
            "category": "algebra",
            "filename": "anderson_badawi_n3.txt",
            "problem_text": "Prove that in any commutative ring R, if an ideal I is 3-absorbing (i.e., whenever abc ∈ I for a,b,c ∈ R, then ab ∈ I or ac ∈ I or bc ∈ I), then I is strongly 3-absorbing.",
            "expected_outcome": "Potential breakthrough extending known n=2 case. Publishable research result if successful.",
            "references": "- [On n-Absorbing Ideals](https://www.researchgate.net/publication/259345078_On_n-Absorbing_Ideals_of_Commutative_Rings)\n- Proven for n=2, open for n≥3",
            "type": "open-problem"
        },
        {
            "title": "Van der Waerden Number W(3,5)",
            "statement": "Compute the exact value of W(3,5): the smallest N such that any 3-coloring of {1,2,...,N} contains a monochromatic 5-term arithmetic progression.",
            "why_tractable": "- W(3,4)=293 found via SAT solving in 2012\n- Natural next case in sequence\n- Proven SAT solving techniques\n- Finite search space with clever pruning",
            "success_rate": 30,
            "time_estimate": "6-8 weeks",
            "difficulty": "Research level",
            "impact": "HIGH - Extends known van der Waerden numbers",
            "mathlib_support": "Low (combinatorics)",
            "category": "combinatorics",
            "filename": "van_der_waerden_w35.txt",
            "problem_text": "Find the smallest positive integer N such that for any 3-coloring of the set {1, 2, ..., N}, there exists a monochromatic arithmetic progression of length 5.",
            "expected_outcome": "Determination of W(3,5) using SAT + formal verification. Major combinatorics result.",
            "references": "- [Van der Waerden number - Wikipedia](https://en.wikipedia.org/wiki/Van_der_Waerden_number)\n- W(3,4)=293 via SAT (2012)",
            "type": "open-problem"
        },
        {
            "title": "Twin Prime Count for p < 10^6",
            "statement": "Prove that there are at least 1000 twin prime pairs (p, p+2) where p < 10^6.",
            "why_tractable": "- Weaker than infinite twin prime conjecture\n- Finite counting problem\n- Builds on Zhang/Maynard bounded gaps work\n- Computational verification + formal proof structure",
            "success_rate": 65,
            "time_estimate": "2 weeks",
            "difficulty": "IMO Problem 5 level",
            "impact": "MEDIUM - Partial result on major problem",
            "mathlib_support": "Good (prime theory)",
            "category": "number-theory",
            "filename": "twin_prime_count.txt",
            "problem_text": "Prove that there exist at least 1000 pairs of twin primes (p, p+2) where both p and p+2 are prime, and p < 1000000.",
            "expected_outcome": "Verification of twin prime density in bounded range. Relates to major open problem.",
            "references": "- [Twin prime - Wikipedia](https://en.wikipedia.org/wiki/Twin_prime)\n- [Zhang's bounded gaps result](https://www.quantamagazine.org/yitang-zhang-proves-landmark-theorem-in-distribution-of-prime-numbers-20130519/)",
            "type": "open-problem"
        },
        {
            "title": "Boolean Schur Number S(4)",
            "statement": "Find the smallest n such that every 4-coloring of {1,2,...,n} contains a monochromatic solution to a + b = c.",
            "why_tractable": "- S(3) solved via massive SAT computation (Boolean Pythagorean Triples)\n- Proven Cube-and-Conquer SAT methodology\n- Natural next case\n- Finite but challenging search",
            "success_rate": 25,
            "time_estimate": "6-8 weeks",
            "difficulty": "Research level",
            "impact": "HIGH - Extends famous SAT solving breakthrough",
            "mathlib_support": "Low (combinatorics)",
            "category": "combinatorics",
            "filename": "schur_s4.txt",
            "problem_text": "Find the smallest positive integer n such that for any 4-coloring of {1, 2, ..., n}, there exist a, b, c in the same color class with a + b = c.",
            "expected_outcome": "Potential determination of S(4) via SAT + verification. Major computational mathematics result.",
            "references": "- [Schur number - Wikipedia](https://en.wikipedia.org/wiki/Schur_number)\n- [Boolean Pythagorean Triples via Cube-and-Conquer](https://arxiv.org/abs/1605.00723)",
            "type": "open-problem"
        },
        {
            "title": "Frankl's Union-Closed Sets Conjecture",
            "statement": "For every finite union-closed family F of sets (other than {∅}), prove there exists an element that appears in at least |F|/2 sets.",
            "why_tractable": "- Claimed solved in 2024, verification ongoing\n- Proven computationally for |∪F| ≤ 11\n- Systematic verification for small universe sizes\n- Clear finite formulation",
            "success_rate": 45,
            "time_estimate": "4 weeks",
            "difficulty": "Research level",
            "impact": "HIGH - If verified, confirms 2024 claimed solution",
            "mathlib_support": "Medium (set theory)",
            "category": "combinatorics",
            "filename": "frankl_conjecture.txt",
            "problem_text": "Prove that for any finite union-closed family F of sets (where F is closed under taking unions and F ≠ {∅}), there exists an element x that appears in at least half of the sets in F.",
            "expected_outcome": "Potential verification of claimed 2024 proof. Major combinatorics breakthrough if confirmed.",
            "references": "- [Union-closed sets conjecture - Wikipedia](https://en.wikipedia.org/wiki/Union-closed_sets_conjecture)\n- [Claimed solution 2024](https://arxiv.org/abs/2405.03731)",
            "type": "open-problem"
        },
        {
            "title": "Brocard's Conjecture for p_n, n ≤ 1000",
            "statement": "For all primes p_n where n ≥ 2 and n ≤ 1000, prove that there are at least 4 primes between p_n² and p_{n+1}².",
            "why_tractable": "- Verified computationally for very large n\n- Finite verification with prime counting\n- Clear bounds and verification strategy\n- Related to prime gaps (well-studied)",
            "success_rate": 70,
            "time_estimate": "2 weeks",
            "difficulty": "IMO Problem 4 level",
            "impact": "MEDIUM - Bounded verification of interesting conjecture",
            "mathlib_support": "Good (prime theory)",
            "category": "number-theory",
            "filename": "brocard_conjecture.txt",
            "problem_text": "For all n where 2 ≤ n ≤ 1000, prove that there are at least 4 prime numbers in the interval (p_n², p_{n+1}²), where p_n is the n-th prime.",
            "expected_outcome": "Verification of Brocard's conjecture for bounded range. Demonstrates prime distribution understanding.",
            "references": "- [Brocard's problem - Wikipedia](https://en.wikipedia.org/wiki/Brocard's_problem)\n- Verified for very large primes",
            "type": "open-problem"
        },
    ],
    "TIER_3": [
        {
            "title": "Ramsey Number R(5,5) [MOONSHOT]",
            "statement": "Determine the exact value of the Ramsey number R(5,5). Currently known: 43 < R(5,5) < 49.",
            "why_tractable": "- Most famous small Ramsey number still unknown\n- Recent SAT solving advances\n- Finite search space (6 possible values)\n- Computational approaches increasingly viable",
            "success_rate": 5,
            "time_estimate": "Months (continuous)",
            "difficulty": "Research level - major breakthrough",
            "impact": "EXTREME - Would be celebrated discovery",
            "mathlib_support": "Low (Ramsey theory)",
            "category": "combinatorics",
            "filename": "ramsey_r55.txt",
            "problem_text": "Determine the exact value of R(5,5): the minimum number of vertices n such that any 2-coloring of the edges of the complete graph K_n contains a monochromatic K_5.",
            "expected_outcome": "If successful: major breakthrough in Ramsey theory. Even improved bounds would be significant.",
            "references": "- [Ramsey's theorem - Wikipedia](https://en.wikipedia.org/wiki/Ramsey's_theorem)\n- Famous unsolved problem, 43 < R(5,5) < 49",
            "type": "open-problem"
        },
        {
            "title": "Irrationality of ζ(5) [MOONSHOT]",
            "statement": "Prove that ζ(5) = 1 + 1/2⁵ + 1/3⁵ + 1/4⁵ + ... is irrational.",
            "why_tractable": "- ζ(3) proven irrational by Apéry (1978)\n- Similar structure suggests similar techniques might work\n- Mathlib has zeta function support\n- Potential for automated insight discovery",
            "success_rate": 15,
            "time_estimate": "Months (continuous)",
            "difficulty": "Research level - stunning if solved",
            "impact": "VERY HIGH - Would extend Apéry's result",
            "mathlib_support": "Good (special functions)",
            "category": "analysis",
            "filename": "zeta_5_irrational.txt",
            "problem_text": "Prove that the value of the Riemann zeta function at 5, defined as ζ(5) = Σ(n=1 to ∞) 1/n⁵, is an irrational number.",
            "expected_outcome": "If successful: stunning breakthrough extending Apéry's result. Even partial progress valuable.",
            "references": "- [Apéry's theorem - Wikipedia](https://en.wikipedia.org/wiki/Apéry's_theorem)\n- [Note on attempts](https://arxiv.org/html/2411.16774)",
            "type": "open-problem"
        },
        {
            "title": "Burnside Problem B(2,5) Finiteness [MOONSHOT]",
            "statement": "Determine whether the free Burnside group B(2,5) (2 generators, exponent 5) is finite.",
            "why_tractable": "- B(r,2), B(r,3), B(r,4), B(r,6) all proven finite\n- Natural next case\n- Computational verification of finite presentations possible\n- Specific, well-defined problem",
            "success_rate": 20,
            "time_estimate": "Months (continuous)",
            "difficulty": "Research level - significant breakthrough",
            "impact": "VERY HIGH - Extends known Burnside results",
            "mathlib_support": "Medium (group theory)",
            "category": "algebra",
            "filename": "burnside_b25.txt",
            "problem_text": "Determine whether the free Burnside group B(2,5), which is the group with 2 generators where every element has order dividing 5, is finite. If finite, determine its order.",
            "expected_outcome": "If successful: major breakthrough in group theory. Resolves natural next case of Burnside problem.",
            "references": "- [Burnside problem - Wikipedia](https://en.wikipedia.org/wiki/Burnside_problem)\n- Known: B(r,2), B(r,3), B(r,4), B(r,6) finite",
            "type": "open-problem"
        },
        {
            "title": "Inverse Galois Problem for M₂₃ [MOONSHOT]",
            "statement": "Prove that the Mathieu group M₂₃ is realizable as a Galois group over ℚ.",
            "why_tractable": "- All other sporadic simple groups known to be realizable\n- Last remaining sporadic case\n- Single finite group, well-understood structure\n- Potential for constructive approach",
            "success_rate": 10,
            "time_estimate": "Months (continuous)",
            "difficulty": "Research level - major breakthrough",
            "impact": "VERY HIGH - Completes sporadic group classification",
            "mathlib_support": "Medium (Galois theory)",
            "category": "algebra",
            "filename": "inverse_galois_m23.txt",
            "problem_text": "Prove that there exists a Galois extension K/ℚ such that the Galois group Gal(K/ℚ) is isomorphic to the Mathieu group M₂₃.",
            "expected_outcome": "If successful: completes Inverse Galois Problem for all sporadic simple groups. Major breakthrough.",
            "references": "- [Inverse Galois problem - Wikipedia](https://en.wikipedia.org/wiki/Inverse_Galois_problem)\n- Last sporadic simple group case",
            "type": "open-problem"
        },
        {
            "title": "Hadwiger-Nelson Problem [MOONSHOT]",
            "statement": "Determine the chromatic number χ of the plane (unit distance graph in ℝ²). Currently: 5 ≤ χ ≤ 7.",
            "why_tractable": "- Lower bound raised to 5 in 2018 (recent progress!)\n- Smallest 5-chromatic graph has 509 vertices\n- Finite graph analysis possible\n- Polymath project actively working on it",
            "success_rate": 10,
            "time_estimate": "Months (continuous)",
            "difficulty": "Research level - major breakthrough",
            "impact": "VERY HIGH - Famous geometric problem",
            "mathlib_support": "Low (geometric combinatorics)",
            "category": "combinatorics",
            "filename": "hadwiger_nelson.txt",
            "problem_text": "Determine the minimum number of colors needed to color the plane such that no two points at unit distance have the same color. Prove whether this chromatic number is 5, 6, or 7.",
            "expected_outcome": "If successful: resolves famous geometric coloring problem. Even improved bounds significant.",
            "references": "- [Hadwiger-Nelson problem - Wikipedia](https://en.wikipedia.org/wiki/Hadwiger–Nelson_problem)\n- [Lower bound 5 (2018)](https://arxiv.org/abs/1804.02385)",
            "type": "open-problem"
        },
        {
            "title": "Collatz Conjecture [EXTREME MOONSHOT]",
            "statement": "Prove that for any positive integer n, the Collatz sequence (3n+1 if odd, n/2 if even) eventually reaches 1.",
            "why_tractable": "- Simple statement\n- Verified computationally to 2^71\n- Automated termination proving techniques exist\n- Worth attempting despite 'hopeless' reputation",
            "success_rate": 0.1,
            "time_estimate": "Indefinite",
            "difficulty": "Unsolved since 1937 - 'completely out of reach'",
            "impact": "EXTREME - Would be mathematical sensation",
            "mathlib_support": "Good (recursion, termination)",
            "category": "number-theory",
            "filename": "collatz_general.txt",
            "problem_text": "Prove that for every positive integer n, if we repeatedly apply the function f(n) = n/2 if n is even, f(n) = 3n+1 if n is odd, we eventually reach 1.",
            "expected_outcome": "Extremely unlikely to succeed, but worth background attempt. Even partial insights valuable.",
            "references": "- [Collatz conjecture - Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)\n- Lagarias: 'completely out of reach'",
            "type": "open-problem"
        },
    ]
}

def create_issue(problem, tier, labels):
    """Create a single GitHub issue"""

    # Determine milestone
    if tier == "TIER_1":
        milestone = "Phase 1: Validation"
    elif tier == "TIER_2":
        milestone = "Phase 2: Research Results"
    else:
        milestone = "Phase 3: Moonshot Hunting"

    # Build label list
    tier_labels = {
        "TIER_1": "tier-1-high-probability",
        "TIER_2": "tier-2-research",
        "TIER_3": "tier-3-moonshot"
    }
    all_labels = [
        tier_labels[tier],
        problem['category']
    ]

    # Add difficulty label
    if "IMO" in problem['difficulty']:
        all_labels.append("imo-level")
    elif "Research" in problem['difficulty'] or "Millennium" in problem['difficulty']:
        all_labels.append("research-level")

    # Add type label
    all_labels.append(problem['type'])

    # Add impact label
    if problem['impact'].startswith("HIGH") or problem['impact'].startswith("VERY HIGH") or problem['impact'].startswith("EXTREME"):
        all_labels.append("high-impact")

    if problem['mathlib_support'] in ["Good", "Excellent"]:
        all_labels.append("mathlib-contribution")

    # Format body
    body = ISSUE_TEMPLATE.format(**problem)

    # Create issue via gh CLI
    cmd = [
        "gh", "issue", "create",
        "--repo", "kavanaghpatrick/aristotle-math-problems",
        "--title", problem['title'],
        "--body", body,
    ]

    # Add labels
    for label in all_labels:
        cmd.extend(["--label", label])

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        print(f"✅ Created: {problem['title']}")
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed: {problem['title']}")
        print(f"   Error: {e.stderr}")
        return None

def main():
    """Create all GitHub issues"""
    print("=" * 80)
    print("CREATING GITHUB ISSUES FOR ARISTOTLE MATH PROBLEMS")
    print("=" * 80)
    print()

    created_count = 0
    failed_count = 0

    for tier, problems in PROBLEMS.items():
        print(f"\n📊 {tier} ({len(problems)} problems)")
        print("-" * 80)

        for problem in problems:
            url = create_issue(problem, tier, [])
            if url:
                created_count += 1
            else:
                failed_count += 1

            # Rate limit: wait between issues
            time.sleep(2)

    print()
    print("=" * 80)
    print(f"✅ Successfully created: {created_count} issues")
    print(f"❌ Failed: {failed_count} issues")
    print()
    print("🔗 View all issues: https://github.com/kavanaghpatrick/aristotle-math-problems/issues")
    print("=" * 80)

if __name__ == "__main__":
    main()
