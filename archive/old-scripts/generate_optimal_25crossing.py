#!/usr/bin/env python3
"""Generate optimized 25-crossing submission based on Round 1 recommendations."""

import snappy
import json
import re

print("🔬 Generating Optimized 25-Crossing Submission")
print("=" * 70)
print()

# Load our braid words
with open('/Users/patrickkavanagh/math/25crossing_test_knots.json') as f:
    knots_data = json.load(f)

def subscript_to_int(subscript):
    """Convert subscript unicode digits to integer."""
    # Subscripts: ₀=U+2080, ₁=U+2081, ..., ₉=U+2089
    mapping = {'₀': '0', '₁': '1', '₂': '2', '₃': '3', '₄': '4',
               '₅': '5', '₆': '6', '₇': '7', '₈': '8', '₉': '9'}

    regular = ''.join(mapping.get(c, c) for c in subscript)
    return int(regular) if regular.isdigit() else None

def parse_braid(braid_str):
    """Parse braid string to extract operations and signs."""
    # Remove parens and spaces
    clean = braid_str.replace("(", "").replace(")", "").replace(" ", "")

    # Match sigma with subscript digits and optional superscript minus/one
    # Pattern: σ followed by subscript digits, optionally followed by ⁻¹
    ops = re.findall(r'σ[₀-₉]+[⁻¹]*', clean)

    parsed = []
    for op in ops:
        # Extract subscript number
        subscript_match = re.search(r'[₀-₉]+', op)
        if subscript_match:
            idx = subscript_to_int(subscript_match.group())
            sign = -1 if '⁻' in op else 1
            parsed.append((idx, sign))

    return parsed

def braid_to_snappy_format(braid_str):
    """Convert unicode braid to SnapPy format."""
    ops = parse_braid(braid_str)

    # SnapPy format: s1 s2 s1^-1 etc
    snappy_str = ""
    for idx, sign in ops:
        if sign == 1:
            snappy_str += f"s{idx} "
        else:
            snappy_str += f"s{idx}^-1 "

    return snappy_str.strip(), ops

def poly_to_lean_sparse(jones_poly):
    """Convert SnapPy Jones polynomial to Lean SparsePoly format."""
    # Jones polynomial relation: t = A^(-4)
    # So term c*t^k becomes (-4*k, c) in SparsePoly

    terms = []
    try:
        # SnapPy jones_polynomial() returns a LaurentPolynomial
        # Access coefficients as dict
        for deg, coeff in jones_poly.dict().items():
            a_power = -4 * deg  # t^k = A^(-4k)
            terms.append((a_power, int(coeff)))

        # Sort by power (descending)
        terms.sort(key=lambda x: x[0], reverse=True)

        # Format for Lean
        lean_terms = [f"({p}, {c})" for p, c in terms]
        return "[" + ", ".join(lean_terms) + "]"

    except Exception as e:
        print(f"  ⚠️  Error converting polynomial: {e}")
        print(f"  Raw poly: {jones_poly}")
        return None

def generate_knot_info(knot):
    """Generate complete knot information with PD code and Jones polynomial."""

    print(f"Processing {knot['name']}...")
    print(f"  Braid word: {knot['braid_word'][:50]}...")

    try:
        # Convert to SnapPy format
        snappy_braid, braid_ops = braid_to_snappy_format(knot['braid_word'])

        # Determine braid strands (max index + 1)
        max_strand = max(idx for idx, _ in braid_ops)
        num_strands = max_strand + 1

        print(f"  Strands: {num_strands}")
        print(f"  Operations: {len(braid_ops)}")

        # Create braid group and link
        BG = snappy.BraidGroup(num_strands)

        # Parse the braid word
        braid = BG(snappy_braid)

        # Get closure as link
        L = braid.closure()

        # Get crossing number
        crossings = L.crossing_number()
        print(f"  Actual crossings: {crossings}")

        if crossings > 30:
            print(f"  ⚠️  Warning: {crossings} crossings (expected ~25)")

        # Get PD code
        pd_code = L.PD_code()
        print(f"  PD code length: {len(pd_code)}")

        # Compute Jones polynomial
        jones = L.jones_polynomial()
        print(f"  Jones polynomial: {str(jones)[:100]}...")

        # Convert to Lean format
        lean_poly = poly_to_lean_sparse(jones)
        if not lean_poly:
            return None

        print(f"  Lean SparsePoly: {lean_poly[:100]}...")

        # Check if trivial (Jones = 1 would be counterexample!)
        if jones == 1:
            print(f"  🚨 COUNTEREXAMPLE FOUND! Jones = 1")
            return None

        result = {
            "name": knot['name'],
            "braid_word": knot['braid_word'],
            "snappy_braid": snappy_braid,
            "num_strands": num_strands,
            "crossings": crossings,
            "pd_code": pd_code,
            "jones_polynomial_str": str(jones),
            "jones_lean_sparse": lean_poly,
            "braid_ops": braid_ops
        }

        print(f"  ✅ Successfully processed!")
        return result

    except Exception as e:
        print(f"  ❌ Error: {e}")
        import traceback
        traceback.print_exc()
        return None

# Process first knot as test
print("Testing with first knot...")
print()

test_knot = knots_data[0]
result = generate_knot_info(test_knot)

if result:
    print()
    print("=" * 70)
    print("✅ SUCCESS! Sample output:")
    print("=" * 70)
    print(json.dumps(result, indent=2))

    # Save results
    with open('/Users/patrickkavanagh/math/25crossing_optimized_test.json', 'w') as f:
        json.dump(result, f, indent=2)

    print()
    print("💾 Saved to: 25crossing_optimized_test.json")
else:
    print()
    print("❌ Processing failed")
