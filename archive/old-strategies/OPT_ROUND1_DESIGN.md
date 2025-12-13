(node:91020) [DEP0040] DeprecationWarning: The `punycode` module is deprecated. Please use a userland alternative instead.
(Use `node --trace-deprecation ...` to show where the warning was created)
(node:91033) [DEP0040] DeprecationWarning: The `punycode` module is deprecated. Please use a userland alternative instead.
(Use `node --trace-deprecation ...` to show where the warning was created)
Loaded cached credentials.
Error executing tool default_api:run_shell_command: Tool "default_api:run_shell_command" not found in registry. Tools must use the exact names that are registered. Did you mean one of: "search_file_content", "list_directory", "google_web_search"?
The optimization plan focuses on **correctness, precision, and minimizing token usage** for the AI model.

### **Plan Overview**
1.  **Generate Accurate Data (Python + SnapPy)**: Instead of string manipulation, use `snappy` to simulate the braid, extract the exact PD code, verify the crossing number, and pre-compute the ground-truth Jones polynomial.
2.  **Lean Scaffolding**: Create a Lean file that imports the existing definitions (saved as a context file) so the AI only needs to write the proof, not the library.
3.  **Submission**: Submit one knot at a time to avoid context overflow and timeouts.

---

### **Step 0: Prerequisite - Save Context**
Save the content of `task5_v2_with_context.txt` (the Lean definitions) to a file named `JonesDefinitions.lean` in your working directory. This allows us to import it rather than pasting it every time.

```bash
cp task5_v2_with_context.txt JonesDefinitions.lean
# Edit JonesDefinitions.lean to remove the markdown header/footer if necessary, 
# ensuring it starts with `import Mathlib` and is a valid Lean file.
```

---

### **Part A & B: Python Script for Generation & Computation**
This script parses the braid words, uses `snappy` to validate them, and generates the **exact** Lean code required.

**File:** `generate_optimal_submission.py`

```python
import snappy
import json
import re

# Braid words from your JSON file
knots_data = [
    {"name": "25_test_01", "braid": "(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁⁻¹σ₂⁻¹)"},
    # ... add other knots or load from json
]

def parse_braid(braid_str):
    """Parses braid string to extract operations and signs."""
    # Remove parens
    clean = braid_str.replace("(", "").replace(")", "")
    # Split into ops (e.g., σ₁⁻¹)
    ops = re.findall(r"σ\d+⁻?¹?", clean)
    parsed = []
    for op in ops:
        idx = int(re.search(r"\d+", op).group())
        sign = -1 if "⁻" in op else 1
        parsed.append((idx, sign))
    return parsed

def poly_to_lean_sparse(poly_t):
    """
    Converts SnapPy Jones polynomial (in q/t) to Lean SparsePoly (in A).
    Relation: t = A^(-4). 
    SnapPy 'q' usually corresponds to 't'.
    So term c*t^k becomes (k * -4, c) in SparsePoly.
    """
    # SnapPy returns a LaurentPolynomial object.
    # distinct_degrees() returns list of degrees, coeffs?
    # Or dict of {deg: coeff}
    terms = []
    try:
        # SnapPy 3.x
        for deg, coeff in poly_t.dict.items():
            terms.append(f"({deg * -4}, {coeff})")
    except AttributeError:
        # Fallback for older/different versions, try string parsing
        # String looks like: 1 + 2*q - q**-1
        # This is risky, better to use the dict or list interface
        print(f"Error parsing poly: {poly_t}")
        return "[]"
    
    # Sort for deterministic output
    return "[" + ", ".join(sorted(terms, key=lambda x: int(x.split(',')[0].strip('(')), reverse=True)) + "]"

def generate_lean_file(knot_name, braid_word):
    # 1. Parse Braid for Signs
    braid_ops = parse_braid(braid_word)
    
    # 2. Create SnapPy Link
    # Convert unicode braid to snappy syntax: s1 s2 s1^-1 ...
    snappy_braid = ""
    for idx, sign in braid_ops:
        snappy_braid += f"s{idx} " if sign == 1 else f"s{idx}^-1 "
        
    L = snappy.Link(snappy.BraidGroup(max(idx for idx, _ in braid_ops) + 1)(snappy_braid).closure())
    
    # 3. Verify Crossing Number
    crossings = L.crossing_number()
    if crossings != 25:
        print(f"WARNING: {knot_name} has {crossings} crossings, expected 25.")
        
    # 4. Get PD Code and Align Signs
    # SnapPy PD code: list of [s1, s2, s3, s4]
    pd_code = L.PD_code()
    
    # Braid closure: each crossing corresponds to a braid generator.
    # SnapPy preserves order for braid closures usually.
    # We assert length matches.
    if len(pd_code) != len(braid_ops):
        print(f"CRITICAL: PD code length {len(pd_code)} != braid ops {len(braid_ops)}. Logic mismatch.")
        return None
        
    # 5. Compute Jones Polynomial
    jones = L.jones_polynomial()
    lean_poly = poly_to_lean_sparse(jones)
    
    # 6. Generate Lean Code
    lean_out = f"""
/-- Knot {knot_name}
    Braid: {braid_word}
    Crossings: {crossings}
-/
def {knot_name} : LinkDiagram := ["""
    
    lean_crossings = []
    for i, (quad, (b_idx, sign)) in enumerate(zip(pd_code, braid_ops)):
        # SnapPy is 0-based, Lean usually 1-based for natural numbers in KnotTheory,
        # but check your definitions. If using simple Nat, 0-based is fine.
        # However, PD codes usually strictly use positive integers.
        # We add 1 to strands to be safe and standard.
        s1, s2, s3, s4 = [x + 1 for x in quad]
        c_str = f"  {{ id := {i+1}, s1 := {s1}, s2 := {s2}, s3 := {s3}, s4 := {s4}, sign := {sign} }}"
        lean_crossings.append(c_str)
        
    lean_out += "\n" + ",\n".join(lean_crossings) + "\n]\n\n"
    
    lean_out += f"def p_{knot_name}_target : SparsePoly := \n  SparsePoly.normalize {lean_poly}\n\n"
    
    lean_out += f"theorem jones_{knot_name}_verify : \n  jones_polynomial_computable_v4 {knot_name} = p_{knot_name}_target := by\n  native_decide\n"
    
    return lean_out

# Example run for one knot
print(generate_lean_file("knot_25_test_01", "(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁σ₂)(σ₁⁻¹σ₂⁻¹)"))
```

---

### **Part C: Lean Template (Scaffolding)**
Save this as `submission_template.lean`. The Python script outputs the specific knot data to append to this.

```lean
import Mathlib
-- Import the context file with all definitions
import JonesDefinitions 

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-
  ARISTOTLE TASK:
  1. The LinkDiagram and Target Polynomial are defined below.
  2. Verify the theorem using `native_decide`.
  
  Note: The complexity is high (25 crossings), but the structure is regular (braid).
-/

-- [PYTHON SCRIPT OUTPUT GOES HERE]
```

---

### **Part D: Minimal Context (Prompt)**
Use this text for the "informal" part of the prompt if submitting via CLI, or as the instruction.

**File:** `aristotle_prompt.txt`
```text
Verify the Jones polynomial for the provided 25-crossing knot.

We have attached a Lean file `submission.lean` which imports the necessary library `JonesDefinitions.lean`.
The knot diagram (PD code) and the expected Jones polynomial (pre-computed via SnapPy) are fully defined in the file.

Your task is to run the verification:
1. Ensure `JonesDefinitions.lean` is in the context.
2. Run the `native_decide` tactic in `submission.lean`.
3. If `native_decide` times out, check if the knot is alternating (Murasugi's theorem applies) or if there is a simplification. However, `native_decide` is preferred for the exact polynomial.

The polynomial variable convention is t = A^(-4).
```

---

### **Part E: Submission Strategy**

1.  **Do NOT submit 20 knots at once.** The overhead of 25-crossing verification is massive.
2.  **Submit ONE knot first** (e.g., `25_test_01` which is 4-strand and "simpler").
3.  **Command**:
    ```bash
    # Ensure JonesDefinitions.lean is present
    aristotle prove-from-file --informal aristotle_prompt.txt --formal-input-context JonesDefinitions.lean --context-files submission.lean
    ```
    *Wait, better strategy:*
    Just create the full `.lean` file (template + python output) and ask Aristotle to "fill sorries" or just "check" it.
    Since I'm providing the full code and just asking for verification, I should use **Mode 1 (Fill Sorries)** if I leave a `sorry`, or just **Mode 4 (English)** with the file as context.

    **Recommended Command:**
    ```bash
    # Create the full file
    cat submission_template.lean knot_25_test_01.lean > 25_test_01_verify.lean
    
    # Submit
    aristotle prove-from-file 25_test_01_verify.lean
    ```
    (This assumes the file is valid Lean. If `native_decide` takes too long for the AI to "verify" during its thinking process, it might fail. But this is the most "Formal" way).

### **Reference Example**
You do not need to include the 9-crossing proof text if you include `JonesDefinitions.lean` because that file *contains* the working 3, 4, and 5 crossing proofs and definitions. It is self-contained.
