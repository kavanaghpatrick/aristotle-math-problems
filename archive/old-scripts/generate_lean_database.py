#!/usr/bin/env python3
"""
Generate Lean 4 code for knot database from JSON files.
Part of Jones Unknotting Conjecture project.
"""

import json
import re
from pathlib import Path


def sanitize_name(name: str) -> str:
    """Convert knot name to valid Lean identifier."""
    # Replace subscript numbers with underscore notation
    name = name.replace('₀', '_0').replace('₁', '_1').replace('₂', '_2')
    name = name.replace('₃', '_3').replace('₄', '_4').replace('₅', '_5')
    name = name.replace('₆', '_6').replace('₇', '_7').replace('₈', '_8')
    name = name.replace('₉', '_9')
    # Replace other special chars
    name = name.replace('-', '_').replace(' ', '_')
    return f"knot_{name}"


def parse_pd_notation(pd_str: str) -> str:
    """Convert PD notation string to Lean list format."""
    # PD notation is like: [[1,5,2,4],[3,1,4,6],[5,3,6,2]]
    # We'll store as string for now, but format nicely
    try:
        pd_list = json.loads(pd_str.replace("'", '"'))
        lean_crossings = []
        for crossing in pd_list:
            lean_crossings.append(f"[{', '.join(map(str, crossing))}]")
        return f"[{', '.join(lean_crossings)}]"
    except:
        # If parsing fails, return as string
        return f'"{pd_str}"'


def generate_knot_entry(knot: dict) -> str:
    """Generate Lean code for a single knot entry."""
    lean_name = sanitize_name(knot['name'])

    # Convert DT notation to Lean list (parse string first)
    dt_str = knot['dt_notation']
    try:
        dt_list = json.loads(dt_str.replace("'", '"'))
        dt_codes = ', '.join(map(str, dt_list))
    except:
        # Fallback: just clean up the string
        dt_codes = dt_str.strip('[]').replace(' ', '')

    # Parse PD notation
    pd_notation = knot['pd_notation']

    # Jones polynomial (optional)
    jones = knot.get('jones_polynomial', '')
    jones_field = f'some "{jones}"' if jones else 'none'

    # Alternating flag
    alternating = str(knot.get('alternating', False)).lower()

    return f"""def {lean_name} : KnotEntry := {{
  name := "{knot['name']}"
  crossings := {knot['crossings']}
  dt_code := {{ codes := [{dt_codes}] }}
  pd_notation_str := "{pd_notation}"
  jones_known := {jones_field}
  alternating := {alternating}
}}
"""


def generate_database_file(json_file: Path, max_crossings: int, output_file: Path):
    """Generate complete Lean database file."""

    with open(json_file) as f:
        knots = json.load(f)

    # Header
    lean_code = f"""/-
Knot Database - Up to {max_crossings} Crossings
Generated from KnotInfo database
Part of Jones Unknotting Conjecture project

Total knots: {len(knots)}
-/

import Mathlib
import «Unknotting».DTCode

-- Individual knot entries
"""

    # Generate entries
    for knot in knots:
        lean_code += generate_knot_entry(knot)
        lean_code += "\n"

    # Generate database list
    lean_code += f"\n-- Complete database ({len(knots)} knots)\n"
    lean_code += f"def knot_database_{max_crossings} : List KnotEntry := [\n"

    knot_names = [sanitize_name(k['name']) for k in knots]
    for i, name in enumerate(knot_names):
        comma = "," if i < len(knot_names) - 1 else ""
        lean_code += f"  {name}{comma}\n"

    lean_code += "]\n\n"

    # Add statistics
    alternating_count = sum(1 for k in knots if k.get('alternating', False))
    lean_code += f"""-- Statistics
-- Total knots: {len(knots)}
-- Alternating: {alternating_count}
-- Non-alternating: {len(knots) - alternating_count}

-- Verify database size
theorem database_{max_crossings}_size :
  knot_database_{max_crossings}.length = {len(knots)} := by native_decide

#check knot_database_{max_crossings}
#eval knot_database_{max_crossings}.length
"""

    # Write output
    with open(output_file, 'w') as f:
        f.write(lean_code)

    print(f"✅ Generated {output_file}")
    print(f"   {len(knots)} knots up to {max_crossings} crossings")
    print(f"   {alternating_count} alternating, {len(knots) - alternating_count} non-alternating")


def main():
    math_dir = Path("/Users/patrickkavanagh/math")

    # Generate for 10 crossings
    generate_database_file(
        json_file=math_dir / "knots_database_10.json",
        max_crossings=10,
        output_file=math_dir / "unknotting" / "KnotDatabase10.lean"
    )

    # Generate for 12 crossings
    generate_database_file(
        json_file=math_dir / "knots_database_12.json",
        max_crossings=12,
        output_file=math_dir / "unknotting" / "KnotDatabase12.lean"
    )

    print("\n✅ Database generation complete!")
    print("\nNext steps:")
    print("1. Test compilation: cd /Users/patrickkavanagh/math && lake build")
    print("2. Validate against existing 8 knots")
    print("3. Prepare first Aristotle batch")


if __name__ == "__main__":
    main()
