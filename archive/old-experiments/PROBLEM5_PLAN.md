# Problem 5: PCR Space Lower Bounds (n≤15)

**Priority**: MEDIUM
**Success Rate**: 60-70%

---

## Gemini Initial Design

This plan outlines the strategy for proving space lower bounds for Polynomial Calculus Resolution (PCR) on specific Pebbling instances.

### **1. Problem Definition**
**Objective:** Prove space lower bounds for PCR refutations of Pebbling formulas over $\mathbb{F}_2$.
**Metric:** Space = Maximum number of monomials in memory simultaneously during refutation.
**Goal:** Show Space $\ge$ Pebbling Number of the underlying graph.

### **2. Selected Instances (n=10, 12, 15)**
We focus on **Pyramid** and **Grid** graphs, which have well-defined pebbling numbers.

*   **Instance 1: Pyramid-4 (n=10)**
    *   **Graph:** Pyramid of height 4. Layers have 1, 2, 3, 4 nodes.
    *   **Nodes:** 10 total.
    *   **Pebbling Number:** 4.
    *   **Structure:**
        *   Layer 1 (Sink): $v_{1,1}$
        *   Layer 2: $v_{2,1}, v_{2,2}$ (Parents of $v_{1,1}$ are $v_{2,1}, v_{2,2}$)
        *   ...
        *   Layer 4 (Sources): $v_{4,1} \dots v_{4,4}$.

*   **Instance 2: Grid-3x4 (n=12)**
    *   **Graph:** Rectangular Grid of width 3, height 4.
    *   **Nodes:** 12 total.
    *   **Pebbling Number:** Related to $\min(width, height) + 1$.
    *   **Structure:** Directed edges $(i, j) \to (i-1, j)$ and $(i, j) \to (i, j-1)$. Sink at $(1,1)$, Sources at boundaries.

*   **Instance 3: Pyramid-5 (n=15)**
    *   **Graph:** Pyramid of height 5. Layers 1 to 5.
    *   **Nodes:** 15 total.
    *   **Pebbling Number:** 5.

### **3. Pebbling Principles Formulation**
For a DAG $G=(V, E)$, the formula $Peb(G)$ is defined over $\mathbb{F}_2$:

*   **Variables:** One variable $x_v$ per vertex $v \in V$.
*   **Axioms:**
    1.  **Source Axioms:** For each source $s$, $x_s = 1$.
        *   *Polynomial:* $x_s - 1 = 0$
    2.  **Propagation Axioms:** For each internal node $v$ with predecessors $p_1, p_2$, $x_{p_1} \land x_{p_2} \implies x_v$.
        *   *Polynomial:* $x_{p_1} x_{p_2} (1 - x_v) = 0$
    3.  **Sink Axiom:** For the target sink $t$, $x_t = 0$ (negated target).
        *   *Polynomial:* $x_t = 0$
    4.  **Boolean Axioms:** For every variable $x$.
        *   *Polynomial:* $x^2 - x = 0$
    5.  **Complement Axioms (Specific to PCR):** Variables $x$ and $\bar{x}$ are treated distinct but linked.
        *   *Polynomial:* $x + \bar{x} - 1 = 0$

### **4. Lean 4 Representation Strategy**
We will implement a custom PCR verifier in Lean 4.

**Key Definitions:**
```lean
-- Variables identified by Fin n
abbrev Var (n : Nat) := Fin n

-- Monomial: Mapping from vars to power (0 or 1 for PCR/Boolean)
def Monomial (n : Nat) := List (Var n) -- Sorted list of vars

-- Polynomial: Sum of monomials over F2
def Polynomial (n : Nat) := List (Monomial n)

-- PCR Step Types
inductive PCRStep (n : Nat) where
  | Axiom (p : Polynomial n)
  | LinearComb (p q : Polynomial n) (alpha beta : F2)
  | Mult (p : Polynomial n) (v : Var n)
  | Delete (index : Nat) -- Explicit memory management for space tracking

-- Configuration: List of Polynomials currently in memory
def Configuration (n : Nat) := List (Polynomial n)

-- Space Metric
def space (config : Configuration n) : Nat :=
  (config.map (fun p => p.monomials.length)).sum -- Total monomials
```

### **5. Aristotle Prompt**
This prompt is designed to be fed to the Aristotle solver to generate the proof.

> **System**: You are an expert in Proof Complexity and Lean 4.
> **Task**: Construct a Polynomial Calculus Resolution (PCR) refutation for the Pebbling formula on a Pyramid graph of height 4 (n=10 nodes).
> **Objective**: Minimize the "Monomial Space" (max number of monomials stored in memory at any step).
> **Graph Definition**:
> - Nodes: 1..10
> - Edges: (Standard Pyramid structure: children of i are 2i, 2i+1 adapted for 1-based indexing)
> **Axioms**:
> 1. Sources (Layer 4): $x_v - 1 = 0$
> 2. Propagation: $x_{left} x_{right} (1 - x_{node}) = 0$
> 3. Sink (Layer 1): $x_{root} = 0$
> **Constraint**: You must define the sequence of PCR steps (Axiom, Add, Mult) that derives 1=0.
> **Output format**: Lean 4 code defining the `refutation` list.

### **6. Validation Strategy**
1.  **Syntactic Check**: Verify the Lean code compiles and corresponds to the n=10, 12, 15 instances.
2.  **Semantic Check**:
    *   Ensure all axioms are correctly derived from the graph definition.
    *   Verify the sequence of steps legitimately derives 0 (or 1 in the contradiction frame).
3.  **Space Calculation**:
    *   Write a script (Python or Lean) to simulate the refutation step-by-step.
    *   Track the set of active polynomials.
    *   Calculate `max(sum(monomials))` over all steps.
4.  **Success Condition**:
    *   For Pyramid-4: Verified Space $\ge$ 4.
    *   For Pyramid-5: Verified Space $\ge$ 5.
