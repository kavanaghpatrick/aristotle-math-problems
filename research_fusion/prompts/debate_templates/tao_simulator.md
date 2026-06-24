# Tao Simulator — Roleplay-Based Strategic Reasoning

**Purpose:** Simulate Terence Tao's first 3 moves on the problem, using his actual published blog posts and papers as anchoring evidence. The roleplay constraint forces the LLM to access a more reasoned, less generic mode of suggestion.

**When to use:**
- LLM outputs feel too generic / textbook
- Need a working mathematician's heuristic prioritization of approaches
- Want to surface forgotten techniques (Tao's blog has 1000+ posts)
- Want to break the "AI gives 5 generic options" failure mode

**Output shape:** 3 concrete first moves per AI per round, each with: the move (computational, structural, or literature), the Tao blog post citation that suggests this move, and the expected information yield.

**Why Tao specifically:** (a) High coverage — Tao writes on most areas of analytic number theory, additive combinatorics, ergodic theory, harmonic analysis. (b) Public blog — concrete citations possible. (c) Iconic style — emphasizes "the right level of generality", "the smoothed problem", and "the dichotomy".

**Risk:** LLM hallucinates a Tao blog post. Mitigation: require URL + post title, then verify with `gh` or curl. For untrusted citations, mark `[unverified]`.

---

## Sample prompt body

```
ROLEPLAY: You are simulating Terence Tao attacking the open problem:

  {PROBLEM}

Tao is approaching it in 2026 with current AI tools available. Generate his FIRST 3 MOVES. Each move must be:

1. **The move itself** (concrete action): e.g., "Compute the auxiliary function f(n) = ... on the first 10^4 values of n", or "Read the Bilu-Tichy theorem; check whether the variety {(a,b,c) : a²b³ + c²d³ = 2 e²f³} satisfies a Bilu-Tichy hypothesis"
2. **Tao blog post or paper citation** that suggests this move. Provide URL if possible. Example: https://terrytao.wordpress.com/2008/08/13/some-tricks-in-analytic-number-theory/. If you are uncertain about the post, mark it `[citation needs verification]` — DO NOT FABRICATE.
3. **Expected information yield**: What does this move *tell us* about the structure of {PROBLEM}? Concretely: which possibilities does it eliminate, which does it confirm?
4. **Why Tao specifically would make this move**: which of his stylistic priors (the smoothed problem, dichotomy, working at the right level of generality, looking for the right model case, polymath collaboration) does this exemplify?

OUTPUT FORMAT:

### Move 1: [Action]
- Citation: ...
- Yield: ...
- Tao-style reasoning: ...

### Move 2: ...
### Move 3: ...

CONSTRAINTS:
- At least 1 of the 3 moves must be a SMALL CONCRETE COMPUTATION (numerical experiment, sample value, etc.) that takes <1 day of compute
- At least 1 must be a LITERATURE PULL on a specific Tao paper or blog post
- At least 1 must be a STRUCTURAL DECOMPOSITION (smoothing, dichotomy, model case, level-of-generality choice)

After listing the 3 moves, give Tao's likely VERDICT on the problem: is it (a) accessible with current tools, (b) accessible with new tools we'd have to develop, (c) likely requiring a fundamental insight not yet seen, or (d) likely false/needs reformulation? Justify in 2-3 sentences.

REMEMBER: this is roleplay. You are channeling Tao's heuristics, not summarizing his publications. The output should feel like the first 3 moves a working mathematician would make, not a textbook listing.
```

---

## Wiring

```bash
python3 scripts/debate_fusion.py ${PROBLEM} --template tao_simulator --rounds 2
mk debate ${PROBLEM} tao_simulator
```
