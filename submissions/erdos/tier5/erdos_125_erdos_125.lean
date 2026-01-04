/-
Erdős Problem #125: erdos_125
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 100
Generated: 2026-01-04T16:20:16.807463
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
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)
-/

open Nat Pointwise

namespace Erdos125

/-
Let $A = {∑ ε_{k} 3^{k} : ε_{k} ∈ {0,1}}$ be the set of integers which
have only the digits $0, 1$ when written base 3, and $B = {∑ ε_{k} 4^{k} : ε_{k} ∈ {0,1}}$
be the set of integers which have only the digits $0, 1$ when written base 4.
Does $A + B$ have positive density?
-/

@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_125:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_125 :
    ({ x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} } +
      { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }).HasPosDensity ↔ answer(sorry) := by
  sorry

end Erdos125
