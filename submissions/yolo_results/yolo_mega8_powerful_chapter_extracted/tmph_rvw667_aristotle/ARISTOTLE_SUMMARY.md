# Summary of changes for run c788e784-012d-480c-97de-5a50c16e14c8
## Completed: Powerful Numbers Chapter META — Coprimality Theorem

The file `yolo_mega8_powerful_chapter.lean` builds successfully with no `sorry` and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Main Result Proved

**`Nat.powerful_3AP_squarefree_d_coprime`**: If `d > 0` is squarefree and `n, n+d, n+2d` are all powerful numbers, then `Nat.Coprime n d`.

### Proof Strategy

The proof proceeds in two layers:

1. **D1 Structural Lemma** (`powerful_3AP_prime_once_not_dvd`): For any prime `p` with `p ∣ d` but `p² ∤ d`, if `n` and `n+d` are both powerful, then `p ∤ n`. The argument: if `p ∣ n`, then powerful(n) gives `p² ∣ n`; since `p ∣ n+d` too, powerful(n+d) gives `p² ∣ n+d`; subtracting yields `p² ∣ d`, contradicting `p² ∤ d`.

2. **Chapter META**: For squarefree `d`, every prime factor `p` of `d` satisfies `p ∣ d` but `p² ∤ d` (by squarefreeness). Apply the D1 lemma prime-by-prime to conclude no prime divides both `n` and `d`, hence `gcd(n,d) = 1`.

### Additional Results in the File

The file also contains fully proved:
- `Nat.Powerful` definition and basic API (squares, cubes, `1`, infinitude)
- Golomb 1970 parametrization (`powerful_iff_sq_mul_cube`: n is powerful iff n = a²b³ with b squarefree)
- Erdős 938 unconditional gap bound for consecutive powerful 3-APs
- Erdős 364 mod-36 closure for consecutive powerful triples (Beckon 2019)
- Multiperfect-σ₀ exclusion via `IsPrimePow`
- Bridge corollary linking the Golomb form to the coprimality result (`powerful_3AP_squarefree_d_coprime_param`)

### Fixes Applied

Three small API compatibility fixes were needed for Lean 4.28.0/current Mathlib:
- `Nat.exists_prime_and_dvd` argument order (used `by omega` for the `≠ 1` proof)
- `Irreducible.not_unit` replaced with `Nat.isUnit_iff` + `Nat.Prime.one_lt.ne'` pattern for the squarefree contradiction