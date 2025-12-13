#!/bin/bash
# Consult Codex CLI on problem framing optimization

echo "🤖 Consulting Codex CLI on Problem Framing..."
echo "======================================================================"
echo

cat > /tmp/codex_framing_prompt.txt << 'EOF'
You are an expert in AI-assisted theorem proving and Lean 4 proof engineering. Analyze our problem framing for Aristotle AI.

CONTEXT:
We submitted 20 knots at 25-crossing to Aristotle using an informal problem statement. This is beyond the computational state-of-the-art (24 crossings max).

OUR CURRENT FRAMING:
- Method: Informal text input (7.5KB)
- Format: Braid words like "(σ₁σ₂σ₁⁻¹σ₂⁻¹)⁶"
- Instructions: Convert to PD codes, compute Jones polynomial, prove ≠ 1
- Context: Rich background on Jones conjecture, computational strategy hints
- Batch: All 20 knots in one submission

CRITICAL ENGINEERING QUESTIONS:

1. BATCH SIZE OPTIMIZATION:
   - Is 20 knots at once optimal?
   - Would 1-knot-per-submission be safer?
   - Could Aristotle fail on all 20 if one is pathological?
   - What's the trade-off between parallelism and failure isolation?

2. INPUT FORMAT:
   - Braid words (requires conversion) - what we used
   - PD codes (direct representation) - would this be better?
   - Explicit Lean scaffolding with "sorry"s - easier for AI?
   - Which format minimizes Aristotle's workload?

3. CONTEXT LEVEL:
   - 7.5KB context - too much?
   - Minimal: "Prove Jones ≠ 1 for knot X" - better?
   - Does rich context help or create noise for AI?
   - What's optimal information density?

4. PROOF SCAFFOLDING:
   Option A: Full informal (what we did)
   Option B: Partial Lean with strategic "sorry"s
   Option C: Give framework, ask to extend

   Which approach maximizes success rate?

5. INCREMENTAL STRATEGY:
   - Should we have tested ONE 25-crossing knot first?
   - Then scaled if successful?
   - Or is batch submission already optimal?
   - What's the failure risk of all-at-once?

6. REPRESENTATION COMPLEXITY:
   - Braid words → PD codes conversion: Is this a failure point?
   - Should we pre-compute PD codes and provide directly?
   - Would that eliminate a potential error source?

7. COMPUTATIONAL HINTS:
   - We warned about 30-50 term polynomials
   - Does this help Aristotle prepare?
   - Or does it bias toward expecting failure?
   - Should we frame as "hard but doable"?

8. REFERENCE EXAMPLES:
   - Should we include a solved 9-crossing example?
   - "Here's how you did it before, now do this harder case"?
   - Would that help pattern matching?

9. DECISION TREE:
   What would you recommend:
   A. Let current submission run (learn from results)
   B. Cancel and resubmit with better framing
   C. Submit a parallel optimized version
   D. Wait and submit improved batch later

10. FAILURE MODES:
    What could go wrong with current framing?
    - Braid → PD conversion errors?
    - Too much context causing confusion?
    - Batch too large causing timeout?
    - Missing critical scaffolding?

BE SPECIFIC:
- Is our framing optimal?
- What exact changes would improve success rate?
- Should we cancel/resubmit or let it run?
- If resubmitting, provide exact template

Focus on practical engineering, not theory.
EOF

codex exec --sandbox read-only "Read /tmp/codex_framing_prompt.txt and analyze our Aristotle problem framing. Be brutally honest: did we optimize this submission, or should we cancel and resubmit? Provide concrete recommendations for improving success rate."

echo
echo "======================================================================"
echo "✅ Codex analysis complete"
