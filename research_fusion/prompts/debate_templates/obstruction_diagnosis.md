# Obstruction Diagnosis — Why Has This Problem Resisted Attack?

**Purpose:** Identify the structural obstruction(s) that have prevented the open problem from being closed for N years. Name the obstruction concretely: parity problem, sieve barrier, height bound, transcendence gap, lack of a Frey curve, etc.

**When to use:**
- Before starting work on a hard problem (set realistic expectations)
- After failure: classify why
- To decide whether to abandon, attempt a sub-case, or invest in tool-building
- To produce honest cost estimates for a multi-month attack

**Output shape:** Per AI per round: a ranked list of obstructions, each named in concrete number-theoretic / analytic / algebraic vocabulary, with a brief history (when was the obstruction first identified, who tried to circumvent it, what failed).

**Difference from bias_flush:** bias_flush critiques OUR toolkit; obstruction_diagnosis diagnoses the PROBLEM. The obstruction may be one that no current tool addresses.

---

## Sample prompt body

```
OBSTRUCTION DIAGNOSIS for the OPEN PROBLEM:

  {PROBLEM}

This problem has resisted attack for N years (find N if possible). Your job is to identify the STRUCTURAL OBSTRUCTIONS that have prevented its closure.

For each obstruction (aim for 3-5):

### Obstruction N: [Concrete name]

Examples of concrete obstruction names:
- "Parity problem in sieves" (sieves cannot distinguish odd from even numbers of prime factors)
- "Sieve dimension barrier" (sieves require κ < 1)
- "Height bound on rational points" (Falting's is ineffective)
- "Archimedean transcendence gap" (no effective Baker bound)
- "Diophantine obstruction at p=2" (the prime 2 behaves differently)
- "Class number / regulator unbounded" (no effective bound on units)
- "Lack of a Frey curve" (no auxiliary elliptic curve attaches naturally)
- "Polymath bottleneck: no smoothness improvement past κ_0"
- "Selmer rank parity not predictable"
- "Galois deformation space dimensions don't match"

For each obstruction:

- **Name**: Use the standard vocabulary above or coin a precise term
- **Why it applies to {PROBLEM}**: which feature of {PROBLEM} triggers this obstruction
- **History**: When was this obstruction first noted in the literature? Who tried to circumvent it (e.g., Vinogradov, Selberg, Bombieri, Friedlander-Iwaniec, Zhang, Tao, Maynard)? Cite specific papers if you can.
- **Known partial circumventions**: If anyone has crossed this barrier in a special case, name it (e.g., "Friedlander-Iwaniec crossed the parity barrier for primes a²+b⁴").
- **Cost-to-cross estimate**: If we wanted to bypass this obstruction for {PROBLEM}, what is the rough effort? In years × top-mathematicians? Or "unsolved-likely-impossible-with-current-tech"?

After listing your obstructions, rank them by SEVERITY (1=most severe). Then:

1. State the SINGLE most severe obstruction in one sentence.
2. State whether {PROBLEM} can be PARTIALLY ATTACKED (sub-cases, residue classes, bounded ranges) without crossing it.
3. State a HONEST PROBABILITY ESTIMATE (0-100%) that {PROBLEM} will be closed in the next 10 years, given current tools and current rate of progress on adjacent problems.

DO NOT BE OPTIMISTIC FOR ITS OWN SAKE. We need honest obstructions, including potentially "this problem is ~unsolvable with current methods, and AI will not change that within 10 years." Honest pessimism is more valuable than vague optimism.

Counter-prompt for the optimistic case: if you DO believe the obstruction is crossable, name the specific recent advance (Zhang 2013, Maynard 2014, Vesselin 2025, etc.) that suggests so.
```

---

## Wiring

```bash
python3 scripts/debate_fusion.py ${PROBLEM} --template obstruction_diagnosis --rounds 2
mk debate ${PROBLEM} obstruction_diagnosis
```
