# Problem 3: F-Matrix Pentagon Equation Verification

**Priority**: HIGH
**Success Rate**: 70-80%

---

## Gemini Initial Design

Here is the comprehensive plan for verifying F-matrices of fusion categories.

### 1. Pentagon Equation Exact Formulation

The Pentagon Equation asserts the consistency of the associator isomorphism $\alpha_{A,B,C}: (A \otimes B) \otimes C \xrightarrow{\cong} A \otimes (B \otimes C)$. In terms of basis vectors and F-matrices (6j-symbols), it relates five sequences of fusion moves.

For simple objects $a, b, c, d, e$ and intermediate objects $k, l, m, n, p$, the equation is:

$$ \sum_{n} (F^{b,c,d}_g)_{e,n} (F^{a,b,n}_p)_{e,k} (F^{a,n,d}_p)_{k,l} = (F^{a,b,c}_k)_{g,d} (F^{a,k,d}_p)_{g,l} $$

*Note: Indices conventions vary. We will use the standard **left-associative to right-associative** basis mapping $(F^{abc}_d)_{ef}$ representing the map $Hom(e, a \otimes b) \otimes Hom(d, e \otimes c) \to Hom(f, b \otimes c) \otimes Hom(d, a \otimes f)$.*

**The Constraint:**
For every quadruple of objects $(a, b, c, d)$ and every pair of external objects $(p, g)$ (where $p$ is the total product and $g$ is an intermediate), the two paths from $((ab)c)d$ to $a(b(cd))$ must yield identical coefficients.

### 2. SageMath Generation Strategy

We will use SageMath's `FusionRing` class to compute the exact F-matrices. We will generate a JSON database containing the fusion rules and F-matrices for the selected categories.

**Target Categories (10-20 instances):**
We focus on small unitary modular tensor categories (UMTCs) and group categories:
1.  **Fibonacci** (`FusionRing("G2", 1)` type or manually constructed Yang-Lee)
2.  **Ising** (`FusionRing("A1", 2)`)
3.  **$SU(2)_k$** for $k=1, 3, 4$ (`FusionRing("A1", k)`)
4.  **$SU(3)_1$** (`FusionRing("A2", 1)`)
5.  **Cyclic Groups** $\mathbb{Z}_3, \mathbb{Z}_4, \mathbb{Z}_5$ (Group categories $Vec_G$ with non-trivial 3-cocycles if possible, or just trivial F=1 for baseline).

**SageMath Script Specification:**
```python
# generate_f_data.py (Draft)
from sage.all import *
import json

def extract_category_data(ring_name, **kwargs):
    R = FusionRing(ring_name, **kwargs)
    simples = R.fusion_labels()
    
    # Fusion Rules N_{ij}^k
    fusion_rules = {}
    for a in simples:
        for b in simples:
            prod = R(a) * R(b)
            # Store non-zero coefficients
            fusion_rules[f"{a},{b}"] = {str(k): int(c) for k, c in prod.monomial_coefficients().items()}

    # F-Matrices
    # Key: "a,b,c,d" -> Matrix values
    f_matrices = {}
    for a in simples:
        for b in simples:
            for c in simples:
                for d in simples:
                    try:
                        # R.f_matrix(a, b, c, d) returns the F-symbol F^{abc}_d
                        # Note: Sage arguments might be (a, b, c, total_charge) or similar.
                        # We will extract ALL F-matrices for this quadruple
                        # Check Sage docs: F^{abc}_d maps (ab)c -> a(bc) over total charge d
                        for total in simples:
                            F = R.get_f_matrix(a, b, c, total)
                            if F is not None:
                                # Convert exact cyclotomics to string representation or complex float
                                f_matrices[f"{a},{b},{c},{total}"] = [
                                    [str(x) for x in row] for row in F.rows()
                                ]
                    except Exception as e:
                        continue

    return {
        "name": str(R),
        "simples": simples,
        "fusion_rules": fusion_rules,
        "f_matrices": f_matrices
    }

# Generate list
categories_to_generate = [
    ("A1", 1), ("A1", 2), ("A1", 3), ("A2", 1), ("G2", 1)
]

data = [extract_category_data(*args) for args in categories_to_generate]
with open("fusion_categories.json", "w") as f:
    json.dump(data, f, indent=2)
```

### 3. Lean Formalization

We will define a structure for Pre-Fusion Categories and a check for the Pentagon Axiom.

**Lean Definitions:**
```lean
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-- Structure representing the minimal data of a fusion category for verification -/
structure FusionData (Label : Type) [DecidableEq Label] where
  /-- F-matrix components: F a b c d e f is the coefficient corresponding to basis change
      from ((ab)c) to a(bc). 
      Indices: a,b,c are inputs. d is total output. e is intermediate (ab). f is intermediate (bc). -/
  f_symbol : Label → Label → Label → Label → Label → Label → Complex

/-- The Pentagon Axiom Check -/
def check_pentagon {Label : Type} [DecidableEq Label] [Fintype Label] 
  (D : FusionData Label) (a b c d e : Label) : Prop :=
  -- Iterate over all possible intermediate states and total charge 'e'
  ∀ (g : Label) (l : Label), 
    (∑ k, (D.f_symbol b c d g e k) * (D.f_symbol a b k e g l) * (D.f_symbol a k d l g e)) 
    = 
    (D.f_symbol a b c e g d) * (D.f_symbol a d c l g e) -- *Note: Indices to be rigorously matched to Sage output*
    
-- In practice, we will use a 'bool' version with epsilon tolerance for floating point verification
def check_pentagon_float {Label : Type} [DecidableEq Label] [Fintype Label] 
  (D : FusionData Label) (epsilon : Float) : Bool :=
  -- Loop over all a,b,c,d,e ...
  true -- implementation details
```

### 4. Validation Strategy

1.  **Baseline (Success):** Verify the `Vec` category (all F=1).
2.  **MTC (Success):** Verify `Ising` and `Fibonacci` exported from Sage.
3.  **Negative Test (Failure):** Manually perturb one entry in the Fibonacci F-matrix JSON by 0.01 and verify that the Lean script returns `false`.

### 5. Aristotle Prompt

**Role:** Aristotle (Verification Agent)
**Task:** Execute Fusion Category Verification Pipeline

**Prompt:**
> "Aristotle, you are tasked with verifying the structural integrity of fusion categories generated by our mathematical engine.
>
> 1.  **Input:** A JSON file `fusion_categories.json` containing F-matrices for 5+ fusion categories.
> 2.  **Tool:** Use the `verify_pentagon.lean` script provided in the context.
> 3.  **Action:** 
>     - Parse the JSON data.
>     - Map the string-based algebraic numbers to complex approximations (or exact types if supported).
>     - Run the `check_pentagon` function for every category.
> 4.  **Report:** Output a Markdown summary table indicating `PASS/FAIL` for each category. If a category fails, identify the specific object quadruple $(a,b,c,d)$ where the pentagon identity breaks."

### 6. Execution & Files (Project Structure)

*   `scripts/generate_fusion_data.py`: SageMath script.
*   `data/fusion_categories.json`: Generated database.
*   `verification/FusionVerify.lean`: The core logic.
*   `verification/Main.lean`: The runner that reads JSON (via a wrapper or simple parser) and runs the check.
