#!/usr/bin/env python3
"""
Extract proven scaffolding from all proven files.
Builds a reusable library for future Aristotle submissions.

Usage: python3 extract_scaffolding.py [output_file]
"""

import sys
import re
from pathlib import Path
from datetime import datetime

def extract_proven_lemmas(content: str, source_file: str) -> list:
    """Extract proven lemmas/theorems from a Lean file."""
    lemmas = []

    # Split into sections by theorem/lemma
    sections = re.split(r'(?=(?:theorem|lemma)\s+\w+)', content)

    for section in sections:
        # Must start with theorem or lemma
        match = re.match(r'(theorem|lemma)\s+(\w+)', section)
        if not match:
            continue

        decl_type = match.group(1)
        name = match.group(2)

        # Check if this has a complete proof (no sorry)
        if ':= by' in section or ':= native_decide' in section or ':= rfl' in section:
            if 'sorry' not in section:
                # Extract until the next theorem/lemma or end
                # Find the end of the proof
                lines = section.split('\n')
                proof_lines = []
                in_proof = False
                brace_depth = 0

                for line in lines:
                    proof_lines.append(line)

                    # Track braces for block depth
                    brace_depth += line.count('{') - line.count('}')

                    # Check if we might be at end of proof
                    stripped = line.strip()
                    if in_proof and brace_depth == 0:
                        # Could be end of tactic proof
                        if stripped and not stripped.startswith('--'):
                            # Heuristic: empty line or new keyword might signal end
                            pass

                    if ':= by' in line or ':= native_decide' in line or ':= rfl' in line:
                        in_proof = True

                lemma_text = '\n'.join(proof_lines).strip()

                lemmas.append({
                    'name': name,
                    'type': decl_type,
                    'source': source_file,
                    'text': lemma_text,
                })

    return lemmas


def scan_proven_files(base_path: Path) -> list:
    """Scan all proven files and extract lemmas."""
    all_lemmas = []

    # Find all .lean files in proven/
    proven_dir = base_path / "proven"
    if not proven_dir.exists():
        print(f"Warning: proven/ directory not found at {proven_dir}")
        return []

    for lean_file in proven_dir.rglob("*.lean"):
        content = lean_file.read_text()
        rel_path = lean_file.relative_to(base_path)
        lemmas = extract_proven_lemmas(content, str(rel_path))
        all_lemmas.extend(lemmas)
        if lemmas:
            print(f"  Found {len(lemmas)} proven lemmas in {rel_path}")

    return all_lemmas


def categorize_lemmas(lemmas: list) -> dict:
    """Categorize lemmas by topic."""
    categories = {
        'packing': [],
        'covering': [],
        'triangles': [],
        'edges': [],
        'M_edges': [],
        'bridges': [],
        'link_graph': [],
        'fractional': [],
        'other': [],
    }

    for lemma in lemmas:
        name_lower = lemma['name'].lower()
        categorized = False

        for category, keywords in [
            ('fractional', ['fractional', 'packing_weight', 'indicator']),
            ('packing', ['packing', 'maxpacking']),
            ('covering', ['cover', 'tau', 'hitting']),
            ('M_edges', ['m_edge', 'medge']),
            ('triangles', ['triangle', 'clique']),
            ('edges', ['edge', 'sym2']),
            ('bridges', ['bridge', 'interaction']),
            ('link_graph', ['link', 'graph']),
        ]:
            if any(kw in name_lower for kw in keywords):
                categories[category].append(lemma)
                categorized = True
                break

        if not categorized:
            categories['other'].append(lemma)

    return categories


def generate_scaffolding_file(lemmas: list, output_path: Path):
    """Generate a consolidated scaffolding file."""
    categories = categorize_lemmas(lemmas)

    content = f"""/-
Tuza ν=4 Scaffolding Library
Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
Total lemmas: {len(lemmas)}

This file contains all proven lemmas extracted from successful Aristotle runs.
Copy relevant sections to new submissions for maximum success rate.

Based on 203 submissions analysis:
- Files with 7+ proven lemmas: 40.7% success rate
- Files with 0 proven lemmas: 0% success rate

USAGE:
1. Copy the import section
2. Copy relevant category sections
3. Keep only lemmas you need (smaller = faster Aristotle processing)
-/

import Mathlib

open Finset BigOperators Classical

noncomputable section

variable {{V : Type*}} [Fintype V] [DecidableEq V]

"""

    # Add each category
    for category, cat_lemmas in categories.items():
        if not cat_lemmas:
            continue

        content += f"""
-- ═══════════════════════════════════════════════════════════════════════
-- {category.upper()} LEMMAS ({len(cat_lemmas)} lemmas)
-- ═══════════════════════════════════════════════════════════════════════

"""
        for lemma in cat_lemmas:
            content += f"-- Source: {lemma['source']}\n"
            content += lemma['text']
            content += "\n\n"

    output_path.write_text(content)
    return len(lemmas)


def main():
    base_path = Path(__file__).parent.parent

    print("=" * 60)
    print("SCAFFOLDING LIBRARY EXTRACTOR")
    print("=" * 60)
    print()

    print("Scanning proven files...")
    lemmas = scan_proven_files(base_path)

    print()
    print(f"Total proven lemmas found: {len(lemmas)}")

    if not lemmas:
        print("No lemmas found. Exiting.")
        return

    # Categorize
    categories = categorize_lemmas(lemmas)
    print("\nBy category:")
    for cat, cat_lemmas in categories.items():
        if cat_lemmas:
            print(f"  {cat}: {len(cat_lemmas)}")

    # Generate output
    output_path = base_path / "proven" / "scaffolding_library.lean"
    if len(sys.argv) > 1:
        output_path = Path(sys.argv[1])

    count = generate_scaffolding_file(lemmas, output_path)
    print(f"\nGenerated: {output_path}")
    print(f"Total lemmas in library: {count}")


if __name__ == "__main__":
    main()
