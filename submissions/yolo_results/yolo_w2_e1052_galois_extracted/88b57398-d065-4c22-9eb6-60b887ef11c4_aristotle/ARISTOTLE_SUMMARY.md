# Summary of changes for run 88b57398-d065-4c22-9eb6-60b887ef11c4
## Erdős 1052 / Wall k=3 — Formalization Summary

### Mathematical Analysis

The problem asks to prove that for every Lehmer pair (α, β) and every n > 30 with 3 ∣ n, the Lehmer sequence term U_n has a primitive prime divisor.

**Key insight:** This is a trivial corollary of the Bilu–Hanrot–Voutier theorem (2001), which proves the same statement for *all* n > 30 (without the 3 ∣ n restriction). The k=3 stratum simply adds a redundant hypothesis.

### What was formalized (in `RequestProject/Main.lean`)

1. **`lehmer_term`** — Definition of the Lehmer sequence term U_n(α, β) via the standard closed form: (αⁿ - βⁿ)/(α - β) for odd n, and (αⁿ - βⁿ)/(α² - β²) for even n.

2. **`not_root_of_unity`** — The condition that α/β is not a root of unity (∀ k > 0, (α/β)^k ≠ 1).

3. **`bhv_primitive_divisor_gt_30`** — Statement of the Bilu–Hanrot–Voutier theorem: for every Lehmer pair and every n > 30, U_n has a primitive prime divisor. **This carries a `sorry`** — see below.

4. **`erdos_1052_wall_k3`** — The k=3 corollary, **fully proved** from `bhv_primitive_divisor_gt_30` by simply dropping the unused `3 ∣ n` hypothesis.

### Remaining `sorry`

The sole `sorry` is in `bhv_primitive_divisor_gt_30`. The BHV theorem is a major result in analytic number theory (50+ page paper) relying on:
- Baker's theory of linear forms in logarithms
- Extensive computational verification for small cases
- None of this machinery is available in Mathlib

This is consistent with the problem's own assessment ("OPEN in Lean — No formalized proof exists in Mathlib for any primitive-divisor statement at this generality").

### Note on the target signature

The provided target signature had two issues that were corrected:
- `rootsOfUnity` in Mathlib takes a parameter `k : ℕ` and produces a `Subgroup Mˣ`, making `α / β ∉ rootsOfUnity` ill-typed. Replaced with `not_root_of_unity (α / β)` defined as `∀ k > 0, (α/β)^k ≠ 1`.
- `q ∣ lehmer_term α β n` with `q : ℕ` and `lehmer_term : ℤ` required explicit cast `(↑q : ℤ) ∣ lehmer_term α β n`.

### On the Mazur transplant

The informal proof outline suggested an alternative path through Mazur's rational isogeny theorem. As the outline itself notes (Step 4), this bridge is "generally invalid" — the connection between Lehmer sequence divisibility (order of α/β in a residue torus) and reducibility of mod-p Galois representations on an elliptic curve is not established in the Stewart–Voutier–BHV framework. The trivial corollary path via BHV is the correct and only valid approach.