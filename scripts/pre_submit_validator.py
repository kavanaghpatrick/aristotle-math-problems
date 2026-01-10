#!/usr/bin/env python3
"""Pre-submission validator for Erdős problems.
Checks for patterns that will cause Aristotle to fail."""

import os
import sys
import glob
import re

# Patterns that WILL cause failures
FATAL_PATTERNS = {
    'answer(': 'FormalConjectures function not in Mathlib',
    '@[category': 'FormalConjectures attribute not in Mathlib',
}

# Identifiers not in Mathlib (require FormalConjectures)
FC_IDENTIFIERS = [
    'NonTrilinear', 'HasConvexNGon', 'ConvexIndep', 
    'IsSidon', 'IsPerfectDifferenceSet', 'OrdinalCardinalRamsey',
    'IsMadGraphColoring', 'Erdos4For',
]

# Type syntax issues
SYNTAX_ISSUES = [
    (r'Finset ℝ²', 'ℝ² type notation - use EuclideanSpace ℝ (Fin 2)'),
    (r': ℝ²', 'ℝ² type notation'),
]

def validate_file(filepath):
    """Returns list of issues found"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    issues = []
    
    # Check fatal patterns
    for pattern, reason in FATAL_PATTERNS.items():
        if pattern in content:
            issues.append(f"FATAL: '{pattern}' - {reason}")
    
    # Check FC identifiers
    for ident in FC_IDENTIFIERS:
        if re.search(rf'\b{ident}\b', content):
            issues.append(f"MISSING DEF: '{ident}' not in Mathlib")
    
    # Check syntax issues  
    for pattern, reason in SYNTAX_ISSUES:
        if re.search(pattern, content):
            issues.append(f"SYNTAX: {reason}")
    
    return issues

def main():
    tier1 = sorted(glob.glob('submissions/erdos/tier1/*.lean'))
    tier2 = sorted(glob.glob('submissions/erdos/tier2/*.lean'))
    
    all_files = tier1 + tier2
    clean_files = []
    problem_files = []
    
    for f in all_files:
        issues = validate_file(f)
        basename = os.path.basename(f)
        if issues:
            problem_files.append((f, issues))
        else:
            clean_files.append(f)
    
    print("=" * 60)
    print("ERDŐS SUBMISSION VALIDATOR")
    print("=" * 60)
    
    print(f"\n✅ CLEAN FILES ({len(clean_files)} ready to submit):")
    for f in clean_files:
        print(f"   {os.path.basename(f)}")
    
    print(f"\n❌ PROBLEM FILES ({len(problem_files)} need fixes):")
    for f, issues in problem_files:
        print(f"\n   {os.path.basename(f)}:")
        for issue in issues[:3]:  # Show first 3 issues
            print(f"      - {issue}")
    
    print("\n" + "=" * 60)
    print(f"SUMMARY: {len(clean_files)}/{len(all_files)} files ready")
    print("=" * 60)
    
    # Output clean file list for submission
    if clean_files:
        with open('/tmp/clean_erdos_files.txt', 'w') as f:
            f.write('\n'.join(clean_files))
        print(f"\nClean file list saved to /tmp/clean_erdos_files.txt")
    
    return 0 if not problem_files else 1

if __name__ == '__main__':
    sys.exit(main())
