#!/bin/bash


echo "Verifying Issue #20..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #20: Collatz Conjecture [EXTREME MOONSHOT]

PROBLEM STATEMENT:
Prove that for any positive integer n, the Collatz sequence (3n+1 if odd, n/2 if even) eventually reaches 1.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 0.1%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 20,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_20.md" &


echo "Verifying Issue #19..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #19: Hadwiger-Nelson Problem [MOONSHOT]

PROBLEM STATEMENT:
Determine the chromatic number χ of the plane (unit distance graph in ℝ²). Currently: 5 ≤ χ ≤ 7.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 10%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 19,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_19.md" &


echo "Verifying Issue #18..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #18: Inverse Galois Problem for M₂₃ [MOONSHOT]

PROBLEM STATEMENT:
Prove that the Mathieu group M₂₃ is realizable as a Galois group over ℚ.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 10%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 18,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_18.md" &


echo "Verifying Issue #17..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #17: Burnside Problem B(2,5) Finiteness [MOONSHOT]

PROBLEM STATEMENT:
Determine whether the free Burnside group B(2,5) (2 generators, exponent 5) is finite.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 20%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 17,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_17.md" &


echo "Verifying Issue #16..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #16: Irrationality of ζ(5) [MOONSHOT]

PROBLEM STATEMENT:
Prove that ζ(5) = 1 + 1/2⁵ + 1/3⁵ + 1/4⁵ + ... is irrational.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 15%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 16,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_16.md" &


echo "Verifying Issue #15..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #15: Ramsey Number R(5,5) [MOONSHOT]

PROBLEM STATEMENT:
Determine the exact value of the Ramsey number R(5,5). Currently known: 43 < R(5,5) < 49.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 5%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 15,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_15.md" &


echo "Verifying Issue #14..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #14: Brocard's Conjecture for p_n, n ≤ 1000

PROBLEM STATEMENT:
For all primes p_n where n ≥ 2 and n ≤ 1000, prove that there are at least 4 primes between p_n² and p_{n+1}².

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 70%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 14,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_14.md" &


echo "Verifying Issue #13..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #13: Frankl's Union-Closed Sets Conjecture

PROBLEM STATEMENT:
For every finite union-closed family F of sets (other than {∅}), prove there exists an element that appears in at least |F|/2 sets.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 45%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 13,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_13.md" &


echo "Verifying Issue #12..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #12: Boolean Schur Number S(4)

PROBLEM STATEMENT:
Find the smallest n such that every 4-coloring of {1,2,...,n} contains a monochromatic solution to a + b = c.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 25%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 12,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_12.md" &


echo "Verifying Issue #11..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #11: Twin Prime Count for p < 10^6

PROBLEM STATEMENT:
Prove that there are at least 1000 twin prime pairs (p, p+2) where p < 10^6.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 65%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 11,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_11.md" &


echo "Verifying Issue #10..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #10: Van der Waerden Number W(3,5)

PROBLEM STATEMENT:
Compute the exact value of W(3,5): the smallest N such that any 3-coloring of {1,2,...,N} contains a monochromatic 5-term arithmetic progression.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 30%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 10,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_10.md" &


echo "Verifying Issue #9..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #9: Anderson-Badawi Conjecture (n=3)

PROBLEM STATEMENT:
Prove that every 3-absorbing ideal of a commutative ring is strongly 3-absorbing.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 50%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 9,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_9.md" &


echo "Verifying Issue #8..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #8: Fortune's Conjecture for n ≤ 1000

PROBLEM STATEMENT:
For all n ≤ 1000, verify that the Fortunate number m_n (the smallest integer m > 1 such that primorial p_n# + m is prime) is itself prime.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 75%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 8,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_8.md" &


echo "Verifying Issue #7..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #7: Linear Diophantine Equations (General Algorithm)

PROBLEM STATEMENT:
For given integers a, b, c, implement and verify a complete algorithm to find all integer solutions to ax + by = c, or prove that no solutions exist.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 99%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 7,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_7.md" &


echo "Verifying Issue #6..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #6: IMO Cyclic Inequality (A5/A6 Level)

PROBLEM STATEMENT:
For positive real numbers a, b, c, prove that:
a³/(b²+c²) + b³/(c²+a²) + c³/(a²+b²) ≥ (a+b+c)/2

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 60%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 6,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_6.md" &


echo "Verifying Issue #5..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #5: Lagrange's Four-Square Theorem

PROBLEM STATEMENT:
Prove that every positive integer can be expressed as the sum of at most four perfect squares. Additionally, characterize which numbers require exactly four squares (those of the form 4^a(8b+7)).

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 80%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 5,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_5.md" &


echo "Verifying Issue #4..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #4: Fermat Number F₅ Compositeness

PROBLEM STATEMENT:
Prove that the fifth Fermat number F₅ = 2^32 + 1 is composite by exhibiting its complete factorization: F₅ = 641 × 6700417.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 98%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 4,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_4.md" &


echo "Verifying Issue #3..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #3: McKay Conjecture Formalization

PROBLEM STATEMENT:
Formalize the McKay conjecture in Lean 4: For a finite group G and prime p, the number of irreducible characters of G with degree not divisible by p equals the same number for the normalizer of a Sylow p-subgroup.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 75%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 3,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_3.md" &


echo "Verifying Issue #2..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #2: Sum of Two Squares Characterization

PROBLEM STATEMENT:
Prove that a positive integer n is expressible as the sum of two squares (n = a² + b²) if and only if in its prime factorization, every prime of the form 4k+3 appears to an even power.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 95%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 2,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_2.md" &


echo "Verifying Issue #1..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: CRITICAL VERIFICATION TASK - Issue #1: Goldbach Conjecture for n ≤ 10^6

PROBLEM STATEMENT:
Prove that every even integer n where 4 ≤ n ≤ 1,000,000 can be expressed as the sum of two prime numbers.

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is \"bounded case\" actually interesting?)
   - Look for \"almost solved\" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., \"prove n+0=n\")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: 85%
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
\`\`\`json
{
  \"issue_number\": 1,
  \"verdict\": \"KEEP | REFORMULATE | REJECT\",
  \"still_unsolved\": true/false,
  \"confidence\": \"HIGH | MEDIUM | LOW\",
  \"formalizability\": \"EASY | MEDIUM | HARD | VERY HARD\",
  \"true_success_probability\": \"X%\",
  \"red_flags\": [\"list\", \"of\", \"concerns\"],
  \"recommended_refinements\": [\"specific\", \"improvements\"],
  \"proof_strategies\": [\"strategy1\", \"strategy2\"],
  \"key_obstacles\": [\"obstacle1\", \"obstacle2\"],
  \"preparatory_steps\": [\"step1\", \"step2\"],
  \"reasoning\": \"detailed explanation of your assessment\"
}
\`\`\`

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.


Output findings to verification-results/codex_result_1.md" &

