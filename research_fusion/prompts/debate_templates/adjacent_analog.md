# Adjacent Analog — Cross-Domain Problem Matching

**Purpose:** Identify 3-5 problems in ADJACENT MATHEMATICAL DOMAINS that share the *structural shape* of the target problem, and name the technique that unlocked each. The goal is technique transfer by analogy.

**When to use:**
- Need to find prior art before attempting a novel attack
- Stuck choosing between competing techniques
- Want to build a literature dossier of "problems shaped like this one"
- Want to falsify the assumption that the problem is "totally new"

**Output shape:** 3-5 named problems per AI per round, each with: problem name + statement, the technique that closed it, the year and proof author, and the explicit structural map from that problem to {PROBLEM}.

**Difference from technique_scout:** Technique-scout asks "what tool"; adjacent-analog asks "what other problem looks like this." Often the analog reveals the tool, but the analog itself is the unit.

---

## Sample prompt body

```
You are matching the OPEN PROBLEM to its structural analogs in adjacent domains:

  {PROBLEM}

For each analog, your job is to name a closed (proven) problem in another domain that has the SAME STRUCTURAL SHAPE as {PROBLEM}. "Same structural shape" means: the same type of object, the same type of quantifier nesting, the same kind of finiteness/density question, or the same Diophantine ingredient.

OUTPUT FORMAT (3-5 analogs per response):

### Analog N: [Name of closed problem]

- **Statement:** [precise statement of the closed problem]
- **Closed by:** [author, year, key paper]
- **Technique:** [specific technique — e.g., "Falting's theorem applied to a fiber product of superelliptic curves"]
- **Structural map to {PROBLEM}:** Explicitly describe the bijection: what plays the role of the variable, the bound, the existential witness, etc. State which features map cleanly and which DO NOT.
- **Transfer feasibility:** Given the dirty parts of the map, what would need to be invented for the technique to actually transfer? Estimate effort in person-months.

Examples of "structural shape" to think about:
- "Find finitely many X with property P" where P is a polynomial Diophantine condition → Falting's, Siegel, Bilu-Tichy
- "Density 0 of X in Y" where Y is a sparse multiplicative sequence → Ergodic theory (Furstenberg correspondence)
- "Existence of infinitely many X" where X is a prime arithmetic configuration → Sieve theory, Zhang, GPY, Maynard
- "No solutions to f(x) = g(y) for high degree f, g" → Bennett-Skinner Frey method, Bilu-Hanrot-Voutier
- "Bound on the gap between consecutive X" → Sieve gaps, Maynard-Tao, Banks-Freiberg-Maynard

For {PROBLEM}, find the closed problem that is most STRUCTURALLY ISOMORPHIC, not just thematically related. "Both are about primes" is not enough; "both are about counting arithmetic progressions in a sparse multiplicatively-defined set" is.

Rank your analogs by tightness of structural match (1 = isomorphic, 5 = vaguely related).
```

---

## Wiring

```bash
python3 scripts/debate_fusion.py ${PROBLEM} --template adjacent_analog --rounds 3
mk debate ${PROBLEM} adjacent_analog
```
