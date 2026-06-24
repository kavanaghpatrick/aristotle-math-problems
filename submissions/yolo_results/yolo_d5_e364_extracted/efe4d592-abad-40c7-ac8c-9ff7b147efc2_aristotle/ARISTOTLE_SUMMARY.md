# Summary of changes for run efe4d592-abad-40c7-ac8c-9ff7b147efc2
## Erdős Problem 364 — mod-36 closure for consecutive powerful triples

Successfully formalized and proved the theorem in `RequestProject/Main.lean`.

### Statement
If `n`, `n+1`, and `n+2` are all powerful numbers (every prime factor occurs with exponent ≥ 2), then `n % 36 ∈ {7, 27, 35}`.

### Proof structure

1. **Definition.** `Powerful n` is defined as `∀ p, p.Prime → p ∣ n → p² ∣ n`.

2. **Three obstruction lemmas:**
   - `not_powerful_of_mod4_eq2`: If `x ≡ 2 (mod 4)` then `x` is not powerful (2 divides but 4 doesn't).
   - `not_powerful_of_mod9_eq3`: If `x ≡ 3 (mod 9)` then `x` is not powerful (3 divides but 9 doesn't).
   - `not_powerful_of_mod9_eq6`: If `x ≡ 6 (mod 9)` then `x` is not powerful (3 divides but 9 doesn't).

3. **Mod-4 constraint:** Among any three consecutive numbers, one is `≡ 2 (mod 4)` unless `n ≡ 3 (mod 4)`. Case analysis on `n % 4` with the mod-4 obstruction forces `n % 4 = 3`.

4. **Mod-9 constraint:** Among any three consecutive numbers, one is `≡ 3` or `≡ 6 (mod 9)` unless `n % 9 ∈ {0, 7, 8}`. Case analysis on `n % 9` with both mod-9 obstructions forces `n % 9 ∈ {0, 7, 8}`.

5. **CRT combination:** `omega` combines `n % 4 = 3` with `n % 9 ∈ {0, 7, 8}` to yield `n % 36 ∈ {7, 27, 35}`.

The proof compiles with no `sorry`, uses only standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and builds successfully.