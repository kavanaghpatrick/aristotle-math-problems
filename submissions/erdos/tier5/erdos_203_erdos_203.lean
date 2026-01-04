/-
Erdős Problem #203: erdos_203
Tier: 5 - Research Open + High Tractability
Status: open | Prize: no | Tractability: 85
Generated: 2026-01-04T16:20:16.819358
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
# Erdős Problem 203

*Reference:* [erdosproblems.com/203](https://www.erdosproblems.com/203)
-/

namespace Erdos203

/--
Is there an integer $m$ with $(m, 6) = 1$ such that none of $2^k \cdot 3^\ell \cdot m + 1$ are prime,
for any $k, \ell \ge 0$?
-/
@[category research open, AMS 5]
/-
PROOF SKETCH for erdos_203:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_203 : (∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime) ↔ answer(sorry) := by
  sorry

--TODO(rdivyanshu): add statements about covering system and odd integers `m` such that none of 2^k*m + 1 is prime

end Erdos203
