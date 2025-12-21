# Evolutionarily Stable Strategies in Extensive-Form Games: Soundness Verification

## Context

This formalizes the key definitions and soundness theorem from Ganzfried (2025) on computing evolutionarily stable strategies in symmetric extensive-form games of imperfect information.

## Definitions

### Symmetric Extensive-Form Game

A two-player extensive-form game is **symmetric** if:
1. The two players' game trees are isomorphic, including identical information sets and available actions at corresponding nodes
2. All chance moves and their probabilities coincide under this isomorphism
3. The payoff functions satisfy u₁(z) = u₂(π(z)) for every terminal history z, where π is the player-swapping automorphism

### Sequence-Form Representation

For a two-player extensive-form game with perfect recall:
- Let E be a matrix where rows correspond to information sets and columns to action sequences
- Let e be a column vector with 1 in the first position and 0 elsewhere
- Let A be the payoff matrix where Aᵢⱼ gives player 1's payoff when player 1 plays action sequence i and player 2 plays sequence j (multiplied by chance probabilities)

A **realization plan** x is feasible if:
- Ex = e
- x ≥ 0

### Behavioral Strategy

A behavioral strategy σ corresponds to a realization plan x satisfying the feasibility constraints. Let u(σ, τ) denote the expected payoff to a player who plays σ against an opponent playing τ.

### Symmetric Nash Equilibrium (SNE)

A realization plan x* is a **symmetric Nash equilibrium** if:
1. Ex* = e and x* ≥ 0
2. For all feasible y: (x*)ᵀAx* ≥ yᵀAx*

Equivalently, x* is an SNE if there exist vectors p and s such that:
- Ex* = e, x* ≥ 0
- Eᵀp - Ax* - s = 0, s ≥ 0
- x*ᵢsᵢ = 0 for all i (complementary slackness)

### Evolutionarily Stable Strategy (ESS)

**Definition (ESS in Extensive-Form Games):** A behavioral strategy σ* (with realization plan x*) is an **evolutionarily stable strategy** if for every behavioral strategy σ ≠ σ* (with realization plan y ≠ x*), exactly one of the following holds:

1. u(σ*, σ*) > u(σ, σ*), i.e., (x*)ᵀAx* > yᵀAx*
2. u(σ*, σ*) = u(σ, σ*) and u(σ*, σ) > u(σ, σ), i.e., (x*)ᵀAx* = yᵀAx* and (x*)ᵀAy > yᵀAy

## The ESS Test

Given an SNE x* with value v* = (x*)ᵀAx*, consider the following optimization problem:

**Minimize** F(y) = (x*)ᵀAy - yᵀAy

**Subject to:**
- Ey = e, y ≥ 0 (feasibility)
- yᵀAx* = v* (same payoff against incumbent)
- ‖y - x*‖² ≥ δ² (numerically distinct from x*)

## Main Theorem: Soundness of ESS Test

**Theorem:** Let x* be a symmetric Nash equilibrium with v* = (x*)ᵀAx*. Then x* is an evolutionarily stable strategy if and only if one of the following holds:

1. The optimization problem above is infeasible, OR
2. The optimal objective value F* > 0

**Proof:**

(⟹) Suppose x* is an ESS. Consider any feasible y with yᵀAx* = v* and y ≠ x*.

Since x* is an SNE, we have (x*)ᵀAx* ≥ yᵀAx* for all feasible y. The constraint yᵀAx* = v* = (x*)ᵀAx* means y achieves equal payoff against the incumbent.

Since x* is an ESS and condition 1 of the ESS definition fails (we have equality, not strict inequality), condition 2 must hold:
(x*)ᵀAy > yᵀAy

Therefore F(y) = (x*)ᵀAy - yᵀAy > 0 for all such y.

If no such y exists (the feasible region is empty), the problem is infeasible.
Otherwise, F* = min F(y) > 0.

(⟸) Suppose the problem is infeasible or F* > 0. We show x* is an ESS.

Take any y ≠ x* with Ey = e, y ≥ 0.

**Case 1:** yᵀAx* < (x*)ᵀAx* = v*

Then condition 1 of ESS holds: u(σ*, σ*) > u(σ, σ*). ✓

**Case 2:** yᵀAx* = v*

Then y is in the feasible region of the optimization problem (assuming ‖y - x*‖² ≥ δ²).

Since F* > 0, we have F(y) = (x*)ᵀAy - yᵀAy > 0, which means (x*)ᵀAy > yᵀAy.

This gives condition 2 of ESS: equal payoff against incumbent, but x* beats y head-to-head. ✓

**Case 3:** yᵀAx* > (x*)ᵀAx*

This contradicts x* being an SNE (which requires (x*)ᵀAx* ≥ yᵀAx* for all feasible y). ✗ Cannot occur.

Thus for all y ≠ x*, either condition 1 or condition 2 of ESS holds. Therefore x* is an ESS. □

## Corollary: Algorithm Correctness

The ESS test algorithm is **sound**: if it classifies x* as an ESS (either due to infeasibility or F* > 0), then x* genuinely satisfies Definition 4 (ESS in extensive-form games).

## Additional Lemma: ESS Implies SNE

**Lemma:** Every evolutionarily stable strategy is a symmetric Nash equilibrium.

**Proof:** Let σ* be an ESS with realization plan x*. Suppose for contradiction that x* is not an SNE. Then there exists feasible y with yᵀAx* > (x*)ᵀAx*.

But this means u(σ, σ*) > u(σ*, σ*), violating both conditions of the ESS definition (condition 1 requires strict inequality in the opposite direction, condition 2 requires equality).

This contradicts σ* being an ESS. Therefore x* must be an SNE. □
