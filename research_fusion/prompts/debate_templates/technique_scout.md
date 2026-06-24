# Technique Scout — Cross-Domain Technique Discovery

**Purpose:** Identify 5 specific techniques from OTHER mathematical areas (algebraic geometry, modular forms, ergodic theory, etc.) that could unlock an open problem currently being attacked with our default toolkit (bounded `native_decide`, σ-multiplicativity case-splits, Fermat reduction).

**When to use:**
- Stage-2 escalation: bare-gap submission stalled
- 3+ failed approaches recorded in `mk failed <problem>`
- F-team audit flagged the problem as "no cross-domain literature attached"
- Need to break out of the iter1→iter2 default pattern

**Output shape:** 5 named techniques per AI per round, each with: technique name, seminal paper citation, structural analog to our problem, and an explicit critique of why our prior bare-gap attempts failed.

**Anti-pattern:** This is NOT meta-process scouting ("which problem next"). It is content scouting ("what mathematical tool, from which subfield, attacks THIS problem"). If the LLM output drifts into pipeline-process talk, the template has failed.

---

## Sample prompt body

```
You are scouting cross-domain techniques for the OPEN PROBLEM:

  {PROBLEM}

Our pipeline is biased toward:
  (a) bounded `native_decide` finite-range verifications
  (b) σ-multiplicativity case-splits on divisor functions
  (c) Fermat-Little-Theorem reductions to residue classes
  (d) bare-gap submissions to Aristotle (formal Lean 4 solver)

These have produced 2 advances out of 1000+ submissions on this and adjacent problems.

YOUR JOB: Identify 5 SPECIFIC techniques from OTHER mathematical areas that could unlock {PROBLEM}. Each must include:

1. **Technique name** (e.g., "Frey-Hellegouarch curve + Ribet level-lowering", NOT "modular forms generally")
2. **Seminal paper or theorem** with author and year (e.g., "Bennett-Skinner 2004 on ternary Diophantine equations")
3. **Structural analog**: which other problem was unlocked by this technique, and which structural feature of {PROBLEM} is analogous
4. **Diagnosis of why bare-gap attempts failed**: name the specific obstruction (sieve barrier, height bound, parity, missing computable bridge) that our toolkit cannot cross
5. **Mathlib feasibility**: which Mathlib namespace would need to be invoked; what is missing

NON-NEGOTIABLE: at least 3 of your 5 techniques MUST come from outside number theory if {PROBLEM} is in NT. (Cross-domain means cross-domain.) Suggested fields: algebraic geometry, modular forms, ergodic theory, additive combinatorics (e.g. Furstenberg correspondence, Gowers norms), p-adic analysis, Diophantine approximation, dynamics on homogeneous spaces, combinatorial group theory.

FORBIDDEN: do not suggest "try harder with native_decide", "extend the bound", "expand the residue class", "add a computable bridge". Those are our default toolkit. We want OTHER tools.

After listing your 5 techniques, rank them 1-5 by your estimated probability of being the actual unlock, with explicit Bayesian reasoning (prior on the technique's success in adjacent problems × likelihood given {PROBLEM}'s specific structure).
```

---

## Wiring

```bash
# Direct invocation:
python3 scripts/debate.py \
  --context analysis/research_fusion_${PROBLEM}.md \
  --topic "$(sed "s/{PROBLEM}/${PROBLEM}/g" research_fusion/prompts/debate_templates/technique_scout.md)" \
  --rounds 3 \
  --output research_fusion/runs/${PROBLEM}/debates/technique_scout.md

# Via wrapper:
python3 scripts/debate_fusion.py ${PROBLEM} --template technique_scout --rounds 3

# Via mk:
mk debate ${PROBLEM} technique_scout
```
