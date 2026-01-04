/-
Erdős Problem #952: erdos_952
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 95
Generated: 2026-01-04T16:20:16.818931
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

import Mathlib

/-!
# Erdős Problem 952

*References:*
- [erdosproblems.com/952](https://www.erdosproblems.com/952)
- [Wikipedia](https://wikipedia.org/wiki/Gaussian_moat)
-/


namespace Erdos952

/--
Is there an infinite sequence of distinct Gaussian primes $x_1,x_2,\ldots$
such that $\lvert x_{n+1}-x_n\rvert \ll 1$?
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_952:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_952 :
  ∃ (x : ℕ → GaussianInt) (C : ℤ),
    Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  sorry

end Erdos952
