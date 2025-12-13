# Problem 4: Spectral Gap Eigenvalue Verification

**Priority**: MEDIUM-HIGH
**Success Rate**: 60-75%

---

## Gemini Initial Design

Here is the complete execution plan for validating the **Spectral Gap Bounds for Odd-Diameter Graphs** (Problem 3).

### Execution Plan: Graph Spectral Gap Verification

**Objective:** Verify spectral gap bounds for d-regular graphs, specifically targeting the "Odd-Diameter" problem, using a hybrid Python-computation and Lean-verification approach.

#### 1. Graph Generation Algorithms
We will generate three classes of 3-regular ($d=3$) graphs to ensure diversity and cover potential counter-examples.

*   **Algorithm A: Random d-Regular Graphs**
    *   **Method:** Use `networkx.random_regular_graph(d, n)`.
    *   **Purpose:** Establish a baseline for "typical" spectral behavior and validate the pipeline.
*   **Algorithm B: Cayley Graphs (Structured)**
    *   **Method:** Construct Cayley graphs for small finite groups using explicit generating sets.
    *   **Groups:** Symmetric groups ($S_n$), Alternating groups ($A_n$), and Projective Special Linear groups ($PSL(2, q)$).
    *   **Purpose:** These are often optimal expanders (Ramanujan graphs) and are critical for testing tight bounds.
*   **Algorithm C: Random Lifts**
    *   **Method:** Start with a base graph (e.g., $K_4$) and generate a random $k$-lift.
    *   **Purpose:** Lifts preserve the "old" spectrum and add "new" eigenvalues, often allowing fine-tuned control over the spectral gap.

#### 2. Test Set (20 Instances)
All graphs will be 3-regular ($d=3$).

| ID | Type | Parameters | Approx Size ($n$) | Rationale |
|---|---|---|---|---|
| **G01-G05** | Random | $n \in \{10, 14, 20, 50, 100\}$ | 10-100 | Baseline validation. |
| **G06** | Cayley | $S_4$, Gen=$\{(12), (23), (34)\}$ | 24 | Standard solvable group. |
| **G07** | Cayley | $A_5$, Standard Generators | 60 | Smallest non-solvable group. |
| **G08** | Cayley | $PSL(2, 5)$ | 60 | Isomorphic to $A_5$, verifying consistency. |
| **G09** | Cayley | Heisenberg Group $H_3(\mathbb{Z}_3)$ | 27 | Nilpotent group structure. |
| **G10** | Cayley | $SL(2, 7)$ | 336 | Larger, highly structured candidate. |
| **G11-G15** | Lift | Base $K_4$, lift $k \in \{2, 3, 5, 10, 20\}$ | 8-80 | Controlled expansion from complete graph. |
| **G16-G20** | Lift | Base Peterson, lift $k \in \{2, 3, 5, 10, 15\}$ | 20-150 | Lifts of a known strong expander. |

#### 3. Spectral Gap Bounds to Verify
For each graph $G$ with adjacency matrix $A$ and spectrum $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n$:

1.  **Ramanujan Bound (Alon-Boppana):**
    *   **Formula:** $\lambda_2 \le 2\sqrt{d-1}$
    *   **For d=3:** Verify $\lambda_2 \le 2\sqrt{2} \approx 2.8284$.
2.  **Odd-Diameter Bound (Target Problem):**
    *   **Condition:** Check if Diameter $D$ is **odd**.
    *   **Refined Bound:** Verify $\lambda_2 \le 2\sqrt{d-1} - \frac{c}{D^2}$ (testing for existence of tighter bounds).
    *   **Metric:** Compute gap $\Delta = d - \lambda_2$.
    *   **Check:** Is $\Delta$ significantly larger than $3 - 2\sqrt{2} \approx 0.17$?

#### 4. Lean Eigenvalue Computation Support
*   **Library Status:** Lean's `Mathlib` contains spectral theory definitions (`LinearAlgebra.Matrix.Spectrum`) but **does not** have an efficient numerical solver for computing eigenvalues of arbitrary matrices.
*   **Strategy: Oracle + Verification**
    1.  **Python Oracle:** A Python script computes the exact eigenvalues and characteristic polynomial.
    2.  **Lean Verification:** The Lean proof does *not* re-compute the eigenvalues from scratch. Instead, it takes the characteristic polynomial $\chi_A(x)$ (computed by Python) and proves bounds on its roots.
    3.  **Technique:** Use **Sturm Sequences** or root-isolation intervals (computable on rationals) to prove that only one root of $\chi_A(x)$ is greater than the bound $B$.

#### 5. Aristotle Prompt
This prompt is designed to guide Aristotle in generating the verification code.

> **Task: Spectral Gap Verification in Lean 4**
>
> **Context:** We are investigating the spectral gap of d-regular graphs to validate bounds for the "Odd-Diameter Spectral Gap" problem.
>
> **Input Data:**
> - **Graph:** [Insert Name, e.g., Random-3-Reg-N20]
> - **Adjacency Matrix (A):** [Insert Python List of Lists]
> - **Python-Computed $\lambda_2$:** [Insert Value, e.g., 2.45]
> - **Target Bound ($2\sqrt{d-1}$):** 2.8284
> - **Characteristic Polynomial:** [Insert Coeffs]
>
> **Your Goal:**
> Create a Lean 4 file that:
> 1.  **Defines the Matrix:** Define `A` as a `Matrix (Fin n) (Fin n) ℚ`.
> 2.  **States the Bound:** Define a theorem `theorem spectral_gap_check : ∃ (count : ℕ), (roots (charpoly A)).count (λ x, x > 2.8284) = 1`. (Stating that only the trivial eigenvalue $d=3$ exceeds the bound).
> 3.  **Proof Strategy:**
>     - For $N < 15$: Attempt proof by `native_decide` if feasible.
>     - For $N \ge 15$: Provide the formal statement and a sketch of how one would import the Python-computed certificate (e.g., "Assume verified via external oracle for now").
>
> **Output:** Provide the complete, valid Lean 4 code block.

#### 6. Validation (Python Side)
An independent script `verify_spectral_gap.py` will serve as the ground truth:
1.  **Load** the graph adjacency matrix.
2.  **Compute** eigenvalues using `scipy.linalg.eigh` (robust for symmetric matrices).
3.  **Calculate** Diameter $D$ using `networkx.diameter`.
4.  **Compare** $\lambda_2$ against $2\sqrt{d-1}$ and log any violations or near-violations.
5.  **Output** a `verification_results.json` summary for Aristotle to read.
