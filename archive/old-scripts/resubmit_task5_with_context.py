#!/usr/bin/env python3
"""Resubmit Task 5 with Jones v2 code as formal context."""

import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key

async def resubmit_task5():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    print("🔄 RESUBMITTING TASK 5 WITH JONES V2 CONTEXT")
    print("=" * 70)
    print()

    # We need to provide the Jones v2 formalization as context
    # But Aristotle's Python API doesn't support --formal-input-context yet
    # Let's create a combined file instead

    print("Creating combined input file with Jones v2 definitions...")

    # Read Jones v2
    with open("/Users/patrickkavanagh/math/aristotle_proofs/jones_v2_2e358cc4_output.lean", "r") as f:
        jones_v2_code = f.read()

    # Read Task 5 description
    with open("/Users/patrickkavanagh/math/task5_verify_4_knots.txt", "r") as f:
        task5_desc = f.read()

    # Create combined input
    combined_input = f"""Extend the Jones Polynomial Formalization to Four Additional Knots (6₁, 6₂, 6₃, 7₁)

CONTEXT:
Below is the COMPLETE Lean 4 formalization of the Jones polynomial from project 2e358cc4-caf3-4e75-846d-60da35fb9b1e. Use ALL the definitions from this file.

```lean
{jones_v2_code}
```

TASK:
Now extend this formalization to verify the Jones polynomial for four additional knots:
- 6₁ (Stevedore's knot)
- 6₂ (Miller Institute knot)
- 6₃ (Eskimo bowline)
- 7₁ (Septafoil knot)

SPECIFIC REQUIREMENTS:

1. **Import and extend** the definitions above. You have access to:
   - `Crossing`, `LinkDiagram` structures
   - `kauffman_bracket_computable_v4` function
   - `jones_polynomial_computable_v4` function
   - `SparsePoly` representation
   - All helper functions (writhe, init_partition, etc.)

2. **Define the 4 new knots** using PD codes:

**Knot 6₁ (Stevedore)**:
- PD Code: X1425 X7,10,8,11 X3948 X9,3,10,2 X5,12,6,1 X11,6,12,7
- Expected Jones polynomial V(q): q² - q + 2 - 2q⁻¹ + q⁻² - q⁻³ + q⁻⁴
- Variable conversion (q → t⁻¹): t⁻⁴ - t⁻³ + t⁻² - 2t⁻¹ + 2 - t + t²
- 6 crossings, reversible symmetry

**Knot 6₂ (Miller Institute)**:
- PD Code: X1425 X5,10,6,11 X3948 X9,3,10,2 X7,12,8,1 X11,6,12,7
- Expected Jones polynomial V(q): q - 1 + 2q⁻¹ - 2q⁻² + 2q⁻³ - 2q⁻⁴ + q⁻⁵
- Variable conversion (q → t⁻¹): t⁻⁵ - 2t⁻⁴ + 2t⁻³ - 2t⁻² + 2t⁻¹ - 1 + t
- 6 crossings, reversible symmetry

**Knot 6₃ (Eskimo Bowline)**:
- PD Code: X4251 X8493 X12,9,1,10 X10,5,11,6 X6,11,7,12 X2837
- Expected Jones polynomial V(q): −q³ + 2q² − 2q + 3 − 2q⁻¹ + 2q⁻² − q⁻³
- Variable conversion (q → t⁻¹): −t⁻³ + 2t⁻² − 2t⁻¹ + 3 − 2t + 2t² − t³
- 6 crossings, fully amphichiral, signature 0

**Knot 7₁ (Septafoil)**:
- PD Code: X1829 X3,10,4,11 X5,12,6,13 X7,14,8,1 X9,2,10,3 X11,4,12,5 X13,6,14,7
- Expected Jones polynomial V(q): −q⁻¹⁰ + q⁻⁹ − q⁻⁸ + q⁻⁷ − q⁻⁶ + q⁻⁵ + q⁻³
- Variable conversion (q → t⁻¹): −t¹⁰ + t⁹ − t⁸ + t⁷ − t⁶ + t⁵ + t³
- 7 crossings, (7,2)-torus knot (like trefoil is (3,2) and cinquefoil is (5,2))

3. **Convert PD codes** to LinkDiagram format following the exact pattern from Jones v2:
   - Each Xa,b,c,d becomes Crossing with (s1, s2, s3, s4) = (a, b, c, d)
   - Determine crossing signs using the patterns that worked in Jones v2
   - For 7₁ (torus knot): likely all same sign (like trefoil and cinquefoil)
   - For 6₁, 6₂, 6₃: try alternating signs first

4. **Verify using native_decide**:
```lean
def knot_6_1 : LinkDiagram := ...
def p6_1_target : SparsePoly := ... -- Jones polynomial in A variable

theorem jones_6_1_correct :
  jones_polynomial_computable_v4 knot_6_1 = p6_1_target := by native_decide
```

5. **Prove complexity bounds**:
```lean
theorem knot_6_1_complexity : bracket_complexity knot_6_1 ≤ 216 := by native_decide
theorem knot_7_1_complexity : bracket_complexity knot_7_1 ≤ 343 := by native_decide
```

CRITICAL NOTES:
- Use t = A⁻⁴ convention from Jones v2
- Knot Atlas uses q = t⁻¹ in their polynomials
- Expected complexity: 2^7 - 1 = 127 for 6-crossing, 2^8 - 1 = 255 for 7-crossing
- Follow the EXACT same pattern as trefoil/figure-eight/cinquefoil from Jones v2
- If signs don't work, try different combinations like Jones v2 did

OUTPUT:
A complete Lean 4 file with:
- All 4 new knot definitions
- All 4 target Jones polynomials
- 4 verification theorems (native_decide)
- 4 complexity bound theorems
- Total expected: 300-500 lines
"""

    # Write combined input
    combined_path = "/Users/patrickkavanagh/math/task5_v2_with_context.txt"
    with open(combined_path, "w") as f:
        f.write(combined_input)

    print(f"✅ Combined input created: {combined_path}")
    print(f"   Size: {len(combined_input)} characters")
    print()

    # Submit to Aristotle
    print("Submitting to Aristotle...")
    task5_v2_id = await Project.prove_from_file(
        input_file_path=combined_path,
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=False
    )

    print()
    print("=" * 70)
    print("✅ TASK 5 V2 SUBMITTED")
    print("=" * 70)
    print(f"Project ID: {task5_v2_id}")
    print()
    print("This version includes the full Jones v2 code as context,")
    print("so Aristotle can access all the necessary definitions.")
    print()
    print("Expected completion: ~3 hours")
    print("=" * 70)

    # Save project ID
    with open("/Users/patrickkavanagh/math/task5_v2_project_id.txt", "w") as f:
        f.write(f"Task 5 v2 (with Jones v2 context): {task5_v2_id}\n")

    return task5_v2_id

if __name__ == "__main__":
    project_id = asyncio.run(resubmit_task5())
    print(f"\n📝 Project ID saved to: task5_v2_project_id.txt")
