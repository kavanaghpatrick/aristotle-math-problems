/-
Erdős Problem #371: erdos_371
Tier: 6 - Everything Else
Status: open | Prize: no | Tractability: 100
Generated: 2026-01-04T16:20:16.829471
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
# Erdős Problem 371

*Reference:* [erdosproblems.com/371](https://www.erdosproblems.com/371)
-/

namespace Erdos371

/--
Let $P(n)$ denote the largest prime factor of $n$. Show that the set of $n$
with $P(n+1) > P(n)$ has density $\frac{1}{2}$.
-/
@[category research open, AMS 11]
/-
PROOF SKETCH for erdos_371:
Status: open

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/

theorem erdos_371 :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2) := by
  sorry

-- TODO: add the statements from the additional material
end Erdos371
