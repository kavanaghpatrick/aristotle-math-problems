# Method-1 screen: erdos_1041 (Erdős–Herzog–Piranian short-path)

Source: formal-conjectures/FormalConjectures/ErdosProblems/1041.lean (theorem `erdos_1041`, @[category research open])
source_kind: ready-queue | tractability_score 6.49 | prior_attempts 0 | literature CLEAR

## Statement (real, NOT answer-placeholder)
For f monic, deg n ≥ 2, all roots in open unit disk: there exist two roots z1,z2 and a path γ
from z1 to z2 with range γ ⊆ {z : |f(z)| < 1} and Hausdorff-1 length(range γ) < 2.

## open_status: GENUINELY-OPEN
- 46 forum posts on erdosproblems.com/1041; active.
- The Component Lemma (some component of {|f|<1} contains ≥2 roots) is PROVED [EHP58]; the length-<2
  path is the open part.

## Tractability: marginal -> downgrade to deep-structural-frontier
- It is a UNIVERSAL METRIC / EXTREMAL inequality over ALL degree-n polynomials, NOT a witness
  construction. Debate (Gemini+Codex, /tmp/method1_miner2_debate.md) ranked it #1 of 5 but called it
  "marginal", "still a universal metric estimate", "expect ~1%".
- DECISIVE prior-art (web): Tao + AlphaEvolve already attacked it — "for 1041 there was some effort
  figuring out how to provide dual certificates ruling out 'paths of length less than 2,' but the
  AlphaEvolve run did not find any counterexamples." (terrytao.wordpress.com / erdosproblems wiki).
  arXiv 2512.12455, 2312.13673 are recent EHP-lemniscate works. This is an active research frontier
  where leading AI tooling has NOT closed it -> NOT easy-tail; honest Method-1 expectation ~0-1%.

## why_method1 (honest)
Only candidate with an existence/path flavour AND a proved geometric foothold (Component Lemma). If a
short elementary bridge "component-with-two-roots -> length-<2 path" existed, informal-mode authoring
could plausibly formalize it. But the bridge IS the hard core and has resisted Tao/AlphaEvolve. Spend
at most ONE exploratory pass; kill immediately if the sketch needs potential theory / extremal
lemniscate machinery.
