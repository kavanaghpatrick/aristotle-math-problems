/-
Erdős Problem #3: erdos_3
Tier: 5 - Research Open + High Tractability
Status: open | Prize: $5000 | Tractability: 90
Generated: 2026-01-04T16:20:16.819201
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
# Erdős Problem 3

*Reference:* [erdosproblems.com/3](https://www.erdosproblems.com/3)
-/

namespace Erdos3

/--
If $A \subset \mathbb{N} has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_3:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_3 : (∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k) ↔ answer(sorry) := by
  sorry

--TODO(firsching): add the various known bounds as variants.

end Erdos3
