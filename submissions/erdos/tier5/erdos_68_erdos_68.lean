/-
Erdős Problem #68: erdos_68
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 100
Generated: 2026-01-04T16:20:16.811803
-/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 68

*Reference:* [erdosproblems.com/68](https://www.erdosproblems.com/68)
-/

namespace Erdos68

/--
Is
$$\sum_{n=2}^\infty \frac{1}{n!-1}$$
irrational?
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_68:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_68 :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) ↔ answer(sorry) := by
  sorry

/--
$$\sum_{n=2}^\infty \frac{1}{n!-1} = \sum_{n=2}^\infty \sum_{k=1}^\infty \frac{1}{(n!)^k}$$
-/
@[category undergraduate, AMS 11]
theorem sum_factorial_inv_eq_geometric :
    let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
    ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) = ∑' n : ℕ, ∑' k : ℕ, f n k := by
  sorry

end Erdos68
