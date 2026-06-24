## Part 1: Taxonomy Design

Snipe probability here means: chance that a good ≤30-line informal Aristotle sketch produces a real `compiled_advance` within about 10 attempts. It is not a truth-confidence score.

### D1. Literature Status

Values: `novel-open`, `known-proved`, `known-disproved`, `partly-known`, `ambiguous`.

Decision rule: do a quick literature check before submission. If the exact statement or its negation is known, classify it here before considering proof strategy.

Why it predicts success: Aristotle can sometimes port or verify known finite results, but it is unlikely to rediscover deep literature proofs. It also prevents submitting false conjectures as proof targets.

### D2. Quantifier Geometry

Values: `bounded-finite`, `fixed-finite-object`, `finite-reducible-infinite`, `infinite-parametric`, `full-structural`.

Decision rule: parse the outer quantifiers. A numerical bound like `n ≤ 1000` is `bounded-finite`; “for all graphs with property P” is usually `full-structural`.

Why it predicts success: Aristotle’s wins have mostly lived in finite or reducibly finite spaces.

### D3. Certificate Shape

Values: `single-witness`, `small-certificate`, `large-table`, `algorithmic-certificate`, `literature-proof-only`, `none-known`.

Decision rule: ask what a Lean proof would actually check: a witness, a CRT cover, a finite table, a computation, or a human proof.

Why it predicts success: Lean is good at checking certificates. It is bad at inventing missing structure.

### D4. Computational Profile

Values: `tiny`, `chunkable`, `large-but-checkable`, `explosive`, `noncomputational`.

Decision rule: estimate whether the proof could finish under native evaluation / kernel limits without huge external data.

Why it predicts success: several wins were finite computations; several failures were kernel or heartbeat blowups.

### D5. Formalization Surface

Values: `mathlib-native`, `small-bespoke`, `moderate-bespoke`, `large-missing-library`, `research-grade-missing-library`.

Decision rule: check whether the objects already exist naturally in Lean/mathlib: primes, factorials, finite graphs, groups, elliptic curves, analytic continuation, zeta zeros, etc.

Why it predicts success: Aristotle often fails by axiomatizing missing machinery or compiling irrelevant scaffolding.

### D6. Novelty Gap

Values: `mechanical-extension`, `routine-finite`, `known-theorem-port`, `local-lemma-needed`, `new-idea-needed`, `frontier-breakthrough`.

Decision rule: compare the target to prior compiled advances and known proofs. If no nearby skeleton exists, raise the novelty gap.

Why it predicts success: the six advances were not frontier breakthroughs; they were finite checks, constructive searches, or mechanical extensions.

### D7. Failure-Mode Risk

Values: `low`, `medium`, `high-restatement`, `high-axiom-risk`, `high-timeout-risk`.

Decision rule: ask which bad compiled result is most likely: `sorry`, axiomatized prior work, irrelevant theorem, or timeout.

Why it predicts success: `compiled_no_advance` is the dominant outcome, so a taxonomy must predict fake progress, not just proof difficulty.

### D8. Negative Evidence

Values: `positive-analogue`, `no-history`, `long-resistant`, `project-carcass`, `known-obstruction`.

Decision rule: check project logs and the literature. Repeated failed submissions or exhausted standard approaches should be a label, not a footnote.

Why it predicts success: this would have stopped the Tuza ν=4 loop much earlier.

---

## Part 2: Apply to 10 Problems

| # | Problem | D1 Status | D2 Quantifiers | D3 Certificate | D4 Compute | D5 Formalization | D6 Novelty | D7 Risk | D8 Evidence | Snipe |
|---:|---|---|---|---|---|---|---|---|---|---:|
| 1 | Erdős 1: covering congruences with arbitrarily large minimum modulus | `known-disproved` | `full-structural` | `literature-proof-only` | `noncomputational` | `large-missing-library` | `known-theorem-port` if reframed | `high-axiom-risk` | `known-obstruction` | 1 |
| 2 | Erdős 51 / Lemoine: odd `>7 = p + 2q` | `novel-open` | `full-structural` | `none-known` | `noncomputational` | `moderate-bespoke` | `new-idea-needed` | `high-restatement` | `long-resistant` | 1 |
| 3 | Weak Goldbach | `known-proved` | `finite-reducible-infinite` | `literature-proof-only` | `large-but-checkable` externally | `research-grade-missing-library` | `known-theorem-port` | `high-axiom-risk` | `known-proved-heavy` | 2 |
| 4 | Twin primes finite-N: `>10^6` pairs below `10^9` | `known/finite-checkable` | `bounded-finite` | `large-table` or `algorithmic-certificate` | `large-but-checkable` | `mathlib-native` | `routine-finite` | `high-timeout-risk` | `positive-analogue` | 7 |
| 5 | BSD | `novel-open` | `full-structural` | `none-known` | `noncomputational` | `research-grade-missing-library` | `frontier-breakthrough` | `high-restatement` | `long-resistant` | 1 |
| 6 | Riemann Hypothesis | `novel-open` | `full-structural` | `none-known` | `noncomputational` | `research-grade-missing-library` | `frontier-breakthrough` | `high-restatement` | `long-resistant` | 1 |
| 7 | Brocard generic | `novel-open` | `infinite-parametric` | `none-known` for tail | `noncomputational` beyond bounds | `small-bespoke` | `new-idea-needed` | `high-restatement` | `positive bounded analogues` | 2 |
| 8 | Sierpiński 78557 smallest | `novel-open` | `finite-reducible-infinite` but unresolved candidates | `mixed`: cover for 78557, missing witnesses below | `explosive` | `small-bespoke` plus huge primality | `new-computation-needed` | `high-timeout-risk` | `long-resistant distributed search` | 1 |
| 9 | FT family infinite, `p=3`, `q ≡ 71 mod 72` | `novel-open` | `infinite-parametric` | `none-known` | `noncomputational` | `large-missing-library` | `new-idea-needed` | `high-axiom-risk` | `known-obstruction` | 1 |
| 10 | Tuza `ν=4` | `novel-open` | `full-structural` with fixed parameter | `none-known` | `explosive` | `moderate-bespoke` | `new-idea-needed` | `high-restatement` | `project-carcass` | 1 |

Status notes from quick check:

- Erdős covering-system minimum modulus is not open as phrased: Hough proved a universal bound, contrary to Erdős’s expectation. See Annals page: https://annals.math.princeton.edu/2015/181-1/p06 and Erdős Problems summary: https://www.erdosproblems.com/tags/covering%20systems/solved
- Weak Goldbach is known by Helfgott: https://arxiv.org/abs/1312.7748
- Sierpiński 78557 remains computationally unresolved in the “smallest” sense; PrimeGrid-style status pages still list remaining candidate searches. Example: https://www.rieselprime.de/ziki/Seventeen_or_Bust

---

## Part 3: Top Picks

### Top 3 Snipe Candidates

1. **Twin primes finite-N** — best exact target. It is finite, elementary, and certificate-checkable. Main risk is computational scale.
2. **Weak Goldbach** — only because it is known-proved. But the proof is analytically heavy, so this is more a formalization target than a snipe.
3. **Brocard generic, only if split into bounded ranges** — the generic conjecture is not a good target, but the project has already shown bounded Brocard chunks are Aristotle-friendly.

Strictly speaking, only #4 is a strong active candidate as stated.

### Top 3 Do Not Bother

1. **BSD** — frontier arithmetic geometry with no compact certificate and huge missing formalization surface.
2. **Riemann Hypothesis** — same issue, with analytic machinery and no finite reduction.
3. **Tuza `ν=4`** — project-carcass label should dominate. 317 failed submissions is enough evidence to stop.

FT family infinite is also a do-not-bother target because the bounded successes do not transfer to the structural infinite version.

### Most Important Added Dimension

**D8: Negative Evidence** is the most important addition beyond the old rubric.

The existing labels can say “structural-open,” but they do not say “this exact structural target has already consumed hundreds of attempts with no advance.” A `project-carcass` value should automatically block rotation unless the new submission has a genuinely new certificate or finite reduction.

It would have stopped the Tuza ν=4 loop far earlier. Separately, D1 `Literature Status` would have flagged slot739 and Erdős 1 as known-formalization / known-disproof items before treating them as novel candidates.