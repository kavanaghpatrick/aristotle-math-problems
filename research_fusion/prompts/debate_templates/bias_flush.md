# Bias Flush — Adversarial Critique of Our Default Toolkit

**Purpose:** Force the LLMs to critique whether our pipeline's defaults — bounded `native_decide`, σ-multiplicativity case-splits, Fermat reductions, residue-class parametrization — actually apply to the target problem, and to enumerate the techniques we are MISSING.

**When to use:**
- After 3+ failed bare-gap submissions on the same problem
- When mk failed shows the same failure mode repeating
- Before a strategic pivot (e.g., before abandoning a problem)
- To check whether iter1→iter2 framing is appropriate for THIS problem

**Output shape:** Two lists per AI per round: (a) which of our defaults apply to {PROBLEM} and why, (b) which techniques we are MISSING from our toolkit — named, with seminal references, and a rough estimate of cost-to-add.

**Difference from technique_scout:** technique_scout enumerates new tools; bias_flush also enumerates which OLD tools fail to apply, and demands a critique of the bias itself. It is the more adversarial template.

---

## Sample prompt body

```
ADVERSARIAL CRITIQUE: Our math project has 4 default techniques in its pipeline. They have produced 2 advances out of 1000+ submissions. Critique whether they apply to the OPEN PROBLEM:

  {PROBLEM}

OUR DEFAULT TOOLKIT (the bias):

1. **Bounded `native_decide` verification**: Reduce the conjecture to a finite check on a bounded range (e.g., n ≤ 1000), then let Lean's `native_decide` tactic discharge it by computation. Works when the problem has a finite computable core.

2. **σ-multiplicativity case-split**: Split a divisor-function inequality into prime-power case-splits, then use σ(p^k) = (p^(k+1) - 1)/(p - 1) explicitly. Works for σ, φ, τ -shaped problems.

3. **Fermat-Little-Theorem reduction**: For problems involving residues mod q^p with q prime, use FLT to reduce to (Z/q)^* or its subgroups. Works for Feit-Thompson style problems.

4. **Residue-class parametrization**: Restrict the problem to a single residue class (e.g., n ≡ a mod m), making the search finite or imposing a known multiplicative structure. Works when the obstruction is a covering system.

PART A — APPLICATION CRITIQUE:

For {PROBLEM}, go through each of the 4 defaults and answer:
- Does it apply? (Yes/No/Partially)
- WHY does it apply, or specifically why not? Name the obstruction (e.g., "the variable is not a residue, but an integer admitting a polynomial Diophantine relation").
- If it partially applies, what fragment of {PROBLEM} would it close? Just that fragment — be specific.

PART B — MISSING TECHNIQUES (more important):

Enumerate the techniques we are MISSING — techniques that the structure of {PROBLEM} demands but our toolkit lacks. For each:

- **Name**: e.g., "Iwasawa main conjecture for cyclotomic fields"
- **Why {PROBLEM} demands it**: which structural feature of {PROBLEM} only this technique addresses
- **Mathlib status**: is it in Mathlib? Partial? Absent? (Be honest — if you do not know, say "unknown".)
- **Cost-to-add estimate**: rough person-months to make Aristotle able to invoke this technique

Aim for at least 3 missing techniques. Prefer techniques from outside number theory if {PROBLEM} is in NT — the bias is sharpest within NT.

PART C — BIAS DIAGNOSIS:

In 2-3 sentences, name our project's deepest bias on {PROBLEM}. Examples of bias types:
- "Treating an asymptotic problem as a bounded problem"
- "Reducing a genuinely Diophantine problem to a residue problem"
- "Treating a problem of generic abundance as a problem of explicit construction"
- "Ignoring archimedean/transcendence inputs"

End with: "if I had to bet on one missing tool, it would be ___, and the reason is ___."
```

---

## Wiring

```bash
python3 scripts/debate_fusion.py ${PROBLEM} --template bias_flush --rounds 2
mk debate ${PROBLEM} bias_flush
```
