# Summary of changes for run 3b48300e-b51b-482c-bc7d-6099819f7cfc
I formalized Erdős Problem 1055 (Selfridge's bounded-class conjecture) in `RequestProject/Erdos1055.lean`. The file contains:

**Definitions:**
- `selfridgeClass : ℕ → ℕ` — The Erdős–Selfridge class of a natural number, defined recursively: for a prime `p`, it equals `1 + max{selfridgeClass q : q prime, q ∣ p+1, q > 3}`, where the max over the empty set is 0. Non-primes receive class 0. The recursion terminates because any prime factor `q > 3` of `p + 1` satisfies `q < p` when `p` is prime.
- `leastPrimeOfClass : ℕ → ℕ` — The least prime of a given Selfridge class, defined as `sInf` of the relevant set (returns 0 if empty).

**Proved lemma:**
- `selfridgeClass_eq_one_iff` — A prime `p` has class 1 if and only if `p + 1` is 3-smooth (all prime factors ≤ 3).

**Open conjecture (left as `sorry`):**
- `selfridge_limit` — There exists a uniform constant `M` such that for every `r ≥ 1`, either no prime has class `r`, or the least class-`r` prime `p_r` satisfies `p_r^{1/r} ≤ M`. This is Selfridge's conjecture; Erdős conjectured the opposite (that this quantity tends to ∞).

The definitions were validated computationally: `selfridgeClass 2 = 1`, `selfridgeClass 13 = 2`, `selfridgeClass 37 = 3`, `selfridgeClass 73 = 4`, matching the known values. The file compiles cleanly with only the main conjecture marked as `sorry`.