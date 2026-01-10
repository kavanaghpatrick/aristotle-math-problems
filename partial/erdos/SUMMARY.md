# Erdős Problem #1 & #647 - Submission Results Summary

## ACTUALLY PROVEN (0 sorry in these lemmas):

### Core Bounds (Multiple Files Confirm)

| Lemma | Constant | File(s) |
|-------|----------|---------|
| `lb` | 1/4 | c636fe00, aed38afd |
| `lb_variance` | 1/√3 ≈ 0.577 | c636fe00, aed38afd |
| `erdos_moser_bound` | 1/4 | aed38afd |

### Supporting Lemmas

| Lemma | Description | File |
|-------|-------------|------|
| `variance_identity` | Σ(sum - μ)² = 2^n/4 · Σa² | c636fe00 |
| `variance_lower_bound` | Variance ≥ (n³-n)/12 | c636fe00 |
| `sum_sq_lower_bound` | Σa² ≥ (4^n - 1)/3 | c636fe00 |
| `second_moment_formula` | Second moment relation | c636fe00 |
| `parseval_subset_sums` | Parseval identity | 9373a94f |
| `parseval_sum_distinct` | Σ(count)² = 2^n | 9373a94f |
| `second_moment_collision` | For sum-distinct, Σ(count)² = 2^n | aed38afd |
| `probabilistic_existence` | ∃ sum-distinct of size ≥ log N | aed38afd |
| `expected_collisions` | E[collisions] bound | aed38afd |
| `least_N_3` | min N for n=3 is 4 | 7efc1f8d |

### Erdős 647 (Divisor Function)

| Lemma | Description | File |
|-------|-------------|------|
| `tau_ge_two` | τ(n) ≥ 2 for n ≥ 2 | 87ecdf18 |
| `exists_large_m_plus_tau` | ∃ m with m + τ(m) ≥ n | 87ecdf18 |
| `max_m_plus_tau_unbounded` | Max grows unboundedly | 87ecdf18 |

## NOT PROVEN (still has sorry):

### Main Targets

| Theorem | Target | Gap |
|---------|--------|-----|
| `erdos_1` | C·2^n ≤ N | Factor of √n |
| `lb_strong` | √(2/π) ≈ 0.798 | Gaussian approximation |
| `erdos_647` | ∃ n > 24 with property | No witnesses found |

### Issues Blocking Progress

1. **Fourier approach**: `exp` ambiguity (Real.exp vs Complex.exp)
2. **Gaussian approximation**: Not formalized in Mathlib
3. **Erdős 647**: Computational search in [25, 200] found nothing

## FALSE LEMMAS (Aristotle negated):

| # | Lemma | Counterexample | Problem |
|---|-------|----------------|---------|
| 18 | `least_N_5_eq_16` | {6,9,11,12,13}, N=13 | Min is 13, not 16 |
| 19 | `sum_distinct_implies_sidon` | {2,3,4} | 2+4=3+3 but subset sums distinct |
| 20 | `discrete_entropy_power_naive` | Free variables | Unbound X_entropy |
| 21 | `erdos_1_empty_set_formulation` | N=0, A=∅ | Need A.Nonempty |
| 23 | `hcn_tau_near_max` | n=2520, τ(1260)=36 | HCN sequence incomplete |

## File Inventory

| File | Proven | Sorry | Negated |
|------|--------|-------|---------|
| erdos_1_fourier_PARTIAL.lean | 2 | 3 | 0 |
| erdos_1_lb_strong_independent_PARTIAL.lean | 5 | 2 | 0 |
| erdos_1_sidon_probabilistic_PARTIAL.lean | 5 | 3 | 2 |
| erdos_1_small_n_PARTIAL.lean | 1 | 2 | 1 |
| erdos_1_main_PARTIAL.lean | 0 | 4 | 0 |
| erdos_1_entropy_PARTIAL.lean | 2 | 3 | 1 |
| erdos_647_divisor_PARTIAL.lean | 3 | 3 | 1 |
