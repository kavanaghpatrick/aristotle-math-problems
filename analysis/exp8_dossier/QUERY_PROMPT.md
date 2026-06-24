# LONG-CONTEXT EXPERIMENT QUERY

You are being given a complete dossier (the file E938_DOSSIER.md that follows
this prompt) of every prior submission, every cited paper, every cross-critique
log, every computational verification, every fusion strategy JSON, every Aristotle
capability artifact, and every relevant project context for **Erdős Problem 938**.

Your task: **identify the SINGLE attack vector on E938 that has NOT yet been
tried in any of the 18 prior submissions and that has the highest probability
of resolution.**

## CONSTRAINTS

Your answer MUST satisfy ALL of:

1. **NOVELTY**: The attack vector must NOT appear in any of the 18+ submissions
   listed in §6 of the dossier. Cite the closest existing submission and explain
   how your proposal differs.

2. **CONCRETENESS**: Give a NAMED lemma structure (Lean-statement-level if you
   can), the key cross-domain ingredient (which technique from which paper),
   and an EXPLICIT computational verification step that would corroborate or
   falsify the approach within hours, not months.

3. **COMBINATION OVER REPETITION**: Prefer attack vectors that COMBINE two or
   more of the already-PROVED unconditional results (slot 1315 upper bound,
   slot 1341 Pell infinitude, slot 1343 gcd theorem, slot 1316 square-gap)
   in a way that no individual prior submission did.

4. **WITHIN ARISTOTLE'S CAPABILITY**: Aristotle has the Mathlib infrastructure
   listed in Appendix E. Your attack must NOT require Mathlib infrastructure
   that does not yet exist (e.g., level-lowering, Bombieri-Lang on dim-2 surfaces,
   o-minimal Pila-Wilkie). Use only what Aristotle has demonstrably been able to
   formalize (Pell equations, Nat.factorization, finite-set enumeration, gcd
   structure, square gaps).

5. **DIRECTION-AGNOSTIC**: Either proof of finiteness OR disproof (constructing
   infinitely many consecutive triples) is acceptable. State which direction.

## OUTPUT FORMAT

```
ATTACK VECTOR NAME: [10-word description]

NOVELTY CHECK:
- Closest existing submission: slot ____ (___ approach)
- Why this is different: ...

THE PROPOSED LEMMA(S):
1. Lemma A: [Lean-style statement]
   Proof sketch: ...
2. Lemma B: [Lean-style statement]
   Proof sketch: ...
3. Main theorem combination: ...

CROSS-DOMAIN INGREDIENT:
- Source paper: [arxiv id or DOI]
- Specific theorem/technique used: ...
- Why importable into Mathlib via Aristotle: ...

COMPUTATIONAL VERIFICATION:
- What to compute: ...
- Expected outcome if approach works: ...
- Expected outcome if approach fails: ...
- Runtime estimate: ...

DIRECTION:
- [ ] Proof of finiteness
- [ ] Disproof (construct infinite family of consecutive triples)
- [ ] Either (the verification step decides which)

ARISTOTLE-CAPABILITY CHECK:
- Mathlib modules needed: ...
- Why this is within Aristotle's demonstrated capability: ...

PROBABILITY OF RESOLUTION:
- P(target_resolved=1 in 72h): __%
- Reasoning: ...
```

After your structured answer, give a 2-paragraph "WHY THIS ATTACK IS NEW"
narrative explaining what insight the long-context synthesis surfaced that
the short-context sub-agents missed.

Now BEGIN reading the dossier and analyzing.

---
