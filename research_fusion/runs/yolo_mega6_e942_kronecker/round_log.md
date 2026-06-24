# MEGA-6 6-Round Deep-Iteration Log (May 31 2026)

## Target
Erdős 942 limsup variant:
  atTop.limsup (fun n ↦ (h n : ℕ∞)) = ⊤
where h(n) = #{powerful m : n^2 ≤ m < (n+1)^2}.

## Round 1: Codex xhigh — formal Lean signature
TIMED OUT (Codex CLI hung; signature ultimately drafted by Grok in Round 4)

## Round 2: Grok web-search — Mathlib4 Kronecker audit
RESULT: NO simultaneous Kronecker/Weyl density theorem in Mathlib4 for AddCircle^M.
Confirmed: only `Mathlib.Topology.Instances.AddCircle.DenseSubgroup.denseRange_zsmul_iff` exists (single AddCircle, iff infinite order).
Also: `Mathlib.Dynamics.Ergodic.AddCircleAdd` has only `ergodic_add_left` (single rotation).
NO `AddCircle^M`, NO `ergodic_pi`, NO `Pi.AddCircle`, NO Weyl equidistribution.
Sketch proof from primitives: induction on M using product topology + denseRange_zsmul_iff + Q-linear independence to rule out non-trivial closed-subgroup orbit closures (character orthogonality argument).

## Round 3: Grok adversarial — 7-question audit
(1) Q-LI of (1, p_1^{3/2}, ..., p_M^{3/2}) for distinct primes p_i: CONFIRMED via Besicovitch 1940.
    Rewrite p_i^{3/2} = p_i · √p_i. {1, √p_1, ..., √p_M} Q-LI (Besicovitch). Any relation q_0 + Σ q_i p_i √p_i = 0 has rational coefficients on the Q-LI basis → q_i p_i = 0 → q_i = 0.
(2) Cleaner irrationals? NO — Lindemann-Weierstrass not in Mathlib4; Besicovitch is the elementary route.
(3) Lean tactic proof of simultaneous Kronecker from denseRange_zsmul_iff: induction on M, product topology, Q-LI to exclude proper closed subgroups. Equivalent character-orthogonality argument.
(4) Easier substitute in Mathlib.Dynamics.Ergodic.*? NO — only single ergodic. No multi-torus theorem.
(5) Box-hit analysis: u_i := ⌈n β_i⌉ ∈ [n β_i, (n+1) β_i) iff fract(n β_i) > 1 - β_i. For n ≥ p_max^{3/2}, u_i ≥ 1. CORRECT.
(6) Distinctness from Golomb uniqueness. CORRECT.
(7) limsup = ⊤ in Mathlib: equivalent to ∀ M, ∃ᶠ n in atTop, M ≤ f n (Filter.Frequently). Use Filter.limsup_eq_top_iff_frequently or similar.

## Round 4: Grok — exact Lean 4 / Mathlib4 signatures
Output (saved to grok_proof.txt):
```lean
-- See research_fusion/runs/yolo_mega6_e942_kronecker/grok_proof.txt
```
Key axioms identified: L_LI_sqrt_primes (Besicovitch), L_sim_Kronecker (multi-AddCircle density).

## Round 5: Grok — synthesize informal outline
1500-word informal_proof_outline produced. Honest disclosure: L3+L4 are Mathlib gaps, axiomatized; deliverable is conditional L1+L2+L3+L4 + L5+L6+L7 → limsup = ⊤.

## Round 6: Self-synthesis — final sketch + fusion JSON
This round.

## DECISIONS
- USE FUSION lane (--fusion-lane).
- Cite De Koninck-Luca-Shparlinski 2005 (Bull. Austral. Math. Soc. 71, 11-16) for quantitative h(n) ≥ (log N)^{1/3 + o(1)} infinitely often.
- Cite Erdős "not hard to prove" framing (erdosproblems.com/942).
- Reference slot 1318 Golomb parametrization (UUID 706abe1b-76b9-4455-b002-b285086bb00b) as load-bearing.
- Explicitly disclose L3 (Besicovitch Q-LI of sqrt-primes) and L4 (simultaneous Kronecker on AddCircle^M) as Mathlib4 gaps that Aristotle would either autoformalize or axiomatize.

## SUBMISSION
- Slot: 1337
- UUID: f293e14f-d2e9-47dd-bb1f-eff0f7412d10
- Lane: FUSION (auto-routed to informal mode by safe_aristotle_submit)
- Hash: 0e319856e68afe3e
- Submitted: 2026-05-30T19:25:32 (UTC)
- Informal prompt size: 7286 chars
- Airlock static=58 dynamic=15 (PASSED)

## Final Theorem Targeted
theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤

## Mathlib Gaps (axiomatized in fusion dossier)
1. L3 = L_LI_sqrt_primes : Besicovitch 1940 Q-LI of {1, p_i^{3/2}} for distinct primes (NOT in Mathlib4)
2. L4 = L_sim_Kronecker : simultaneous Kronecker density on AddCircle^M (NOT in Mathlib4)

Mathlib4 has ONLY single-variable denseRange_zsmul_iff (Topology.Instances.AddCircle.DenseSubgroup).
