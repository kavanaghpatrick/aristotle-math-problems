#!/usr/bin/env python3
"""Resubmit both Task 5 and Task 6 with Jones v2 context."""

import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key

async def resubmit_both():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🔄 RESUBMITTING TASKS 5 & 6 WITH JONES V2 CONTEXT")
    print("=" * 70)
    print()

    # Read Jones v2
    print("Loading Jones v2 formalization...")
    with open("/Users/patrickkavanagh/math/aristotle_proofs/jones_v2_2e358cc4_output.lean", "r") as f:
        jones_v2_code = f.read()

    print(f"✅ Jones v2 loaded ({len(jones_v2_code)} characters)")
    print()

    # ==================== TASK 5 ====================
    print("=" * 70)
    print("CREATING TASK 5 V2 (with context)")
    print("=" * 70)

    task5_combined = f"""Extend the Jones Polynomial Formalization to Four Additional Knots (6₁, 6₂, 6₃, 7₁)

CONTEXT - JONES V2 FORMALIZATION:
Below is the COMPLETE Lean 4 formalization from project 2e358cc4. You can use ALL definitions from this code.

```lean
{jones_v2_code}
```

TASK - VERIFY 4 NEW KNOTS:

Use the definitions above (Crossing, LinkDiagram, kauffman_bracket_computable_v4, jones_polynomial_computable_v4, SparsePoly, etc.) to verify 4 additional knots:

**Knot 6₁ (Stevedore's knot)**:
- PD Code: X1,4,2,5 X7,10,8,11 X3,9,4,8 X9,3,10,2 X5,12,6,1 X11,6,12,7
- Jones polynomial V(q): q² - q + 2 - 2q⁻¹ + q⁻² - q⁻³ + q⁻⁴
- In t (where q=t⁻¹): t⁻⁴ - t⁻³ + t⁻² - 2t⁻¹ + 2 - t + t²
- In A (where t=A⁻⁴): Convert to SparsePoly format

**Knot 6₂ (Miller Institute knot)**:
- PD Code: X1,4,2,5 X5,10,6,11 X3,9,4,8 X9,3,10,2 X7,12,8,1 X11,6,12,7
- Jones polynomial V(q): q - 1 + 2q⁻¹ - 2q⁻² + 2q⁻³ - 2q⁻⁴ + q⁻⁵
- In t: t⁻⁵ - 2t⁻⁴ + 2t⁻³ - 2t⁻² + 2t⁻¹ - 1 + t

**Knot 6₃ (Eskimo Bowline)**:
- PD Code: X4,2,5,1 X8,4,9,3 X12,9,1,10 X10,5,11,6 X6,11,7,12 X2,8,3,7
- Jones polynomial V(q): −q³ + 2q² − 2q + 3 − 2q⁻¹ + 2q⁻² − q⁻³
- In t: −t⁻³ + 2t⁻² − 2t⁻¹ + 3 − 2t + 2t² − t³

**Knot 7₁ (Septafoil - (7,2)-torus knot)**:
- PD Code: X1,8,2,9 X3,10,4,11 X5,12,6,13 X7,14,8,1 X9,2,10,3 X11,4,12,5 X13,6,14,7
- Jones polynomial V(q): −q⁻¹⁰ + q⁻⁹ − q⁻⁸ + q⁻⁷ − q⁻⁶ + q⁻⁵ + q⁻³
- In t: −t¹⁰ + t⁹ − t⁸ + t⁷ − t⁶ + t⁵ + t³
- Note: (7,2)-torus knot like trefoil (3,2) and cinquefoil (5,2) - use same sign pattern

REQUIREMENTS:
1. Define knot diagrams using LinkDiagram structure from above
2. Define target polynomials as SparsePoly (in A variable, using t=A⁻⁴)
3. Prove verification theorems using native_decide
4. Prove complexity bounds: ≤ 216 for 6-crossing, ≤ 343 for 7-crossing

Follow the EXACT pattern from trefoil_final, figure_eight_final, cinquefoil_final, three_twist_final in the code above.
"""

    task5_path = "/Users/patrickkavanagh/math/task5_v2_with_context.txt"
    with open(task5_path, "w") as f:
        f.write(task5_combined)

    print(f"✅ Task 5 v2 input created: {task5_path}")
    print(f"   Size: {len(task5_combined)} characters")
    print()

    # ==================== TASK 6 ====================
    print("=" * 70)
    print("CREATING TASK 6 V2 (with context)")
    print("=" * 70)

    task6_combined = f"""Prove Reidemeister Invariance for the Jones Polynomial

CONTEXT - JONES V2 FORMALIZATION:
Below is the COMPLETE Lean 4 formalization from project 2e358cc4. You can use ALL definitions from this code.

```lean
{jones_v2_code}
```

TASK - PROVE REIDEMEISTER INVARIANCE:

Using the definitions above (LinkDiagram, kauffman_bracket_computable_v4, jones_polynomial_computable_v4, writhe, etc.), prove that the Jones polynomial is invariant under Reidemeister moves.

THEORETICAL BACKGROUND:

Reidemeister moves are local transformations that preserve knot equivalence:
- **R1**: Add/remove a kink (twist) - changes writhe by ±1
- **R2**: Add/remove two antiparallel crossings - writhe unchanged
- **R3**: Slide strand over crossing (triangle move) - writhe unchanged

Kauffman Bracket Behavior:
- **R1**: <L'> = (-A³)^±1 · <L> (NOT invariant)
- **R2**: <L'> = <L> (invariant)
- **R3**: <L'> = <L> (invariant)

Jones Polynomial V(t) = (-A³)⁻ʷ⁽ᴸ⁾ · <L>:
- **R1**: Invariant (writhe change compensated by normalization)
- **R2**: Invariant (writhe and bracket both unchanged)
- **R3**: Invariant (writhe and bracket both unchanged)

SPECIFIC TASKS:

1. **Define Reidemeister Moves** as predicates on LinkDiagram pairs:
```lean
-- R1: Adding/removing a kink changes writhe by ±1, bracket by (-A³)^±1
def R1_move (D D' : LinkDiagram) : Prop := ...

-- R2: Two antiparallel crossings that can be removed
def R2_move (D D' : LinkDiagram) : Prop := ...

-- R3: Sliding strand over crossing (triangle configuration)
def R3_move (D D' : LinkDiagram) : Prop := ...
```

2. **Prove Kauffman Bracket R2 Invariance**:
```lean
theorem kauffman_bracket_R2_invariant (D D' : LinkDiagram)
  (h : R2_move D D') :
  kauffman_bracket_computable_v4 D = kauffman_bracket_computable_v4 D' := by
  -- Apply skein relation to both crossings
  -- Show they cancel to yield the same result
  sorry -- You prove this
```

3. **Prove Kauffman Bracket R3 Invariance**:
```lean
theorem kauffman_bracket_R3_invariant (D D' : LinkDiagram)
  (h : R3_move D D') :
  kauffman_bracket_computable_v4 D = kauffman_bracket_computable_v4 D' := by
  -- Most complex case: apply skein relation to all 3 crossings
  -- Expand to smoothing states and show equivalence
  sorry -- You prove this
```

4. **Prove Jones Polynomial R1 Invariance**:
```lean
theorem jones_polynomial_R1_invariant (D D' : LinkDiagram)
  (h : R1_move D D') :
  jones_polynomial_computable_v4 D = jones_polynomial_computable_v4 D' := by
  -- Show writhe changes by ±1: w(D') = w(D) ± 1
  -- Show bracket changes: <D'> = (-A³)^±1 · <D>
  -- Show normalization compensates:
  --   V(D') = (-A³)^(-w(D')​) · <D'>
  --         = (-A³)^(-w(D)∓1) · ((-A³)^±1 · <D>)
  --         = (-A³)^(-w(D)) · <D>
  --         = V(D)
  sorry -- You prove this
```

5. **Optional: General Invariance Theorem**:
```lean
theorem jones_polynomial_reidemeister_invariant (D D' : LinkDiagram)
  (h : ReflTransGen (fun L L' => R1_move L L' ∨ R2_move L L' ∨ R3_move L L') D D') :
  jones_polynomial_computable_v4 D = jones_polynomial_computable_v4 D' := by
  -- Induction on move sequence
  sorry -- You prove this if possible
```

6. **Test Cases** (verify on concrete examples):
```lean
-- Example: Unknot with kink has same Jones polynomial as unknot
example : jones_polynomial_computable_v4 unknot_with_kink =
          jones_polynomial_computable_v4 unknot := by
  sorry -- You prove this as a test case
```

IMPLEMENTATION STRATEGY:

**Start Simple:**
- Begin with R2 invariance (easiest - uses skein relation directly)
- Then R3 invariance (complex but purely diagrammatic)
- Finally R1 invariance (requires writhe normalization)

**Diagram Operations:**
- You may need to extend LinkDiagram to support local modifications
- Define helper functions to identify R-move configurations
- Create functions to perform each move on a diagram

**Proof Techniques:**
- Use native_decide for computational steps
- Use induction for recursive definitions
- Apply skein relations systematically

SUCCESS CRITERIA:
- **Minimum**: R2 invariance proven (acceptable)
- **Target**: R2 + R3 proven (good)
- **Excellent**: Full R1 + R2 + R3 + general theorem (ideal)

OUTPUT:
A complete Lean 4 file extending the Jones v2 formalization with Reidemeister invariance proofs. Expected length: 500-800 lines depending on scope achieved.
"""

    task6_path = "/Users/patrickkavanagh/math/task6_v2_with_context.txt"
    with open(task6_path, "w") as f:
        f.write(task6_combined)

    print(f"✅ Task 6 v2 input created: {task6_path}")
    print(f"   Size: {len(task6_combined)} characters")
    print()

    # ==================== SUBMIT BOTH ====================
    print("=" * 70)
    print("SUBMITTING TO ARISTOTLE")
    print("=" * 70)
    print()

    print("Submitting Task 5 v2...")
    task5_v2_id = await Project.prove_from_file(
        input_file_path=task5_path,
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=False
    )
    print(f"✅ Task 5 v2 submitted: {task5_v2_id}")
    print()

    print("Submitting Task 6 v2...")
    task6_v2_id = await Project.prove_from_file(
        input_file_path=task6_path,
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=False
    )
    print(f"✅ Task 6 v2 submitted: {task6_v2_id}")
    print()

    # Save project IDs
    with open("/Users/patrickkavanagh/math/tasks_v2_project_ids.txt", "w") as f:
        f.write(f"Task 5 v2 (4 Knots with context): {task5_v2_id}\n")
        f.write(f"Task 6 v2 (Reidemeister with context): {task6_v2_id}\n")

    print("=" * 70)
    print("📊 SUBMISSION SUMMARY")
    print("=" * 70)
    print(f"Task 5 v2: {task5_v2_id}")
    print(f"Task 6 v2: {task6_v2_id}")
    print()
    print("Both tasks now have full Jones v2 context.")
    print("Expected completion:")
    print("  - Task 5: ~3 hours")
    print("  - Task 6: ~13 hours")
    print("=" * 70)

    return task5_v2_id, task6_v2_id

if __name__ == "__main__":
    t5, t6 = asyncio.run(resubmit_both())
    print(f"\n✅ Project IDs saved to: tasks_v2_project_ids.txt")
