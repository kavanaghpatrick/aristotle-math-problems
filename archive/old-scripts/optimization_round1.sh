#!/bin/bash
# Optimization Round 1: Get detailed design specs

echo "🔄 OPTIMIZATION ROUND 1: Detailed Design"
echo "======================================================================"
echo

gemini -p "You are an expert in Lean 4, knot theory, and AI-assisted theorem proving. Help design the OPTIMAL submission for 25-crossing knots to Aristotle AI.

CONTEXT:
- We submitted 20 knots with suboptimal framing (batch, braid words, 7.5KB context)
- Both Codex and Grok-2 recommended canceling and optimizing
- Key issues: Too large batch, wrong format, too much context, no scaffolding

YOUR TASK:
Design the OPTIMAL submission strategy from scratch. Be MAXIMALLY SPECIFIC with actual code examples.

CRITICAL DESIGN QUESTIONS:

1. KNOT GENERATION:
   - Exact SnapPy commands to convert braid words to PD codes
   - How to verify crossing count is exactly 25
   - How to verify knot is non-trivial

2. JONES POLYNOMIAL PRECOMPUTATION:
   - Exact SnapPy/Mathematica commands
   - Format for Lean (SparsePoly with A variable where t=A^(-4))
   - Validation strategy

3. LEAN SCAFFOLDING:
   - Exact template structure
   - What imports needed
   - How to represent PD codes in Lean
   - How much to fill vs leave as sorry

4. MINIMAL CONTEXT:
   - Exact 1-2 paragraph template
   - What to include/exclude

5. SUBMISSION STRATEGY:
   - One knot first or small batch?
   - Which knot to test first?
   - Sequential or parallel?

6. REFERENCE EXAMPLE:
   - Should we include solved 9-crossing proof?
   - How to annotate it?

DELIVERABLES:
A. Python script for PD code generation (exact SnapPy commands)
B. Python script for Jones polynomial computation
C. Lean template file (exact syntax)
D. Minimal context template (exact wording)
E. Submission order recommendation

Be MAXIMALLY SPECIFIC. Give actual runnable code." > /tmp/opt_round1_output.txt 2>&1

cat /tmp/opt_round1_output.txt
cat /tmp/opt_round1_output.txt > /Users/patrickkavanagh/math/OPT_ROUND1_DESIGN.md

echo
echo "✅ Round 1 design saved to OPT_ROUND1_DESIGN.md"
