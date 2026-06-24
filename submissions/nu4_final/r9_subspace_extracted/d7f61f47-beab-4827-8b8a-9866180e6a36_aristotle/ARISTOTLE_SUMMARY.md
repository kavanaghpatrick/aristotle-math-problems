# Summary of changes for run d7f61f47-beab-4827-8b8a-9866180e6a36
## Erdős 1003 Fixed-Support Finiteness — Fully Proved

I discovered and formalized a complete, sorry-free proof of the fixed-support finiteness sub-claim of Erdős 1003.

### Mathematical Proof (Key Insight)

The proof avoids the deep S-unit equation machinery (Evertse-Schlickewei-Schmidt) suggested in the problem outline. Instead, it exploits a much simpler observation:

**The ratio φ(n)/n depends only on the set of prime factors of n**, not on their exponents. Specifically, φ(n)/n = ∏_{p|n} (1 − 1/p). This means that if two positive integers n₁, n₂ share the same prime support, then φ(n₁)·n₂ = φ(n₂)·n₁.

The proof constructs an injection from the solution set into a finite set:

1. **Map**: Send each solution n to the pair (prime factors of n in S, prime factors of n+1 in S). The image lives in S.powerset × S.powerset, which is finite.

2. **Injectivity**: Suppose n₁ ≠ n₂ both satisfy φ(n) = φ(n+1) with support in S, and have the same image. Then:
   - Same prime supports give φ(n₁)·n₂ = φ(n₂)·n₁ ... (i)
   - Same prime supports for n+1 give φ(n₁+1)·(n₂+1) = φ(n₂+1)·(n₁+1) ... (ii)
   - Using φ(nᵢ) = φ(nᵢ+1), equation (ii) becomes φ(n₁)·(n₂+1) = φ(n₂)·(n₁+1)
   - Subtracting (i): φ(n₁) = φ(n₂)
   - Back in (i): φ(n₁)·n₂ = φ(n₁)·n₁, and since φ(n₁) > 0, we get n₁ = n₂. ∎

### Formalization Structure (`RequestProject/Erdos1003.lean`)

Three helper lemmas build to the main theorem:

- **`totient_mul_rad_eq`**: The identity φ(n) · rad(n) = n · ∏_{p|n}(p−1), proved using Mathlib's `Nat.totient_eq_div_primeFactors_mul`.

- **`totient_ratio_of_primeFactors_eq`**: If n₁ and n₂ have the same prime factors, then φ(n₁)·n₂ = φ(n₂)·n₁. Derived from the product identity by algebraic manipulation.

- **`primeFactors_eq_filter_of_support_subset`**: When all prime factors of n lie in S, the prime factors equal S filtered by divisibility.

- **`erdos_1003_fixed_support_finite`** (main theorem): Combines the injection into S.powerset × S.powerset with the injectivity argument.

### Verification

- ✅ Builds with zero sorries (`grep -n sorry` finds nothing)
- ✅ Only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- ✅ No linter warnings

### Note on the approach

The informal proof outline suggested using the Evertse-Schlickewei-Schmidt theorem (Annals 2002) on S-unit equations, which is a very deep result absent from Mathlib. The proof I found instead is completely elementary — the φ(n) = φ(n+1) constraint provides enough structure that no S-unit theory is needed. The key is that the totient condition, combined with the support constraint, makes the natural injection into pairs of subsets of S actually injective, giving finiteness immediately.