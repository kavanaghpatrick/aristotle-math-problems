/-
Erdős Problem #705: erdos_705
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 100
Generated: 2026-01-04T16:20:16.811939
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
# Erdős Problem 705

*Reference:* [erdosproblems.com/705](https://www.erdosproblems.com/705)
-/

namespace Erdos705

open scoped EuclideanGeometry
open SimpleGraph

/--
Let G be a finite unit distance graph in R².
Is there some k such that if G has girth ≥ k, then χ(G) ≤ 3?
-/
@[category research open, AMS 5]
/-
PROOF SKETCH for erdos_705:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_705:
  (∀ (V : Set ℝ²) (hf: V.Finite),
    ∃ k, (UnitDistancePlaneGraph V).girth ≥ k ∧ (UnitDistancePlaneGraph V).chromaticNumber ≤ 3) ↔
    answer(sorry) := by sorry


-- TODO: add statements for the concrete constructions in the additional material

end Erdos705
