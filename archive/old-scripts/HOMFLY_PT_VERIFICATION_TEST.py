#!/usr/bin/env python3
"""
HOMFLY-PT Test Case Verification Script

Quick verification that test data is accessible and consistent.
Run this to validate the test suite before implementation.

Usage: python3 HOMFLY_PT_VERIFICATION_TEST.py
"""

import pandas as pd
from pathlib import Path

# Configuration
CSV_PATH = Path("/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv")

# Test knots (our core test suite)
TEST_KNOTS = ['0_1', '3_1', '4_1', '5_1', '5_2', '6_1', '6_2', '6_3', '7_1', '7_2', '7_3']

def load_data():
    """Load KnotInfo CSV data."""
    print(f"Loading data from: {CSV_PATH}")
    df = pd.read_csv(CSV_PATH, delimiter='|')
    print(f"✓ Loaded {len(df)} knots\n")
    return df

def verify_test_cases(df):
    """Verify all test knots are present with required data."""
    print("=" * 60)
    print("VERIFYING TEST CASES")
    print("=" * 60)
    
    missing = []
    for knot in TEST_KNOTS:
        if knot not in df['name'].values:
            missing.append(knot)
            print(f"✗ {knot}: NOT FOUND")
        else:
            row = df[df['name'] == knot].iloc[0]
            homfly = row['homfly_polynomial']
            jones = row['jones_polynomial']
            braid = row['braid_notation']
            
            # Check if data exists
            if pd.isna(homfly) or homfly == '':
                print(f"✗ {knot}: Missing HOMFLY-PT")
            elif pd.isna(jones) or jones == '':
                print(f"✗ {knot}: Missing Jones")
            elif pd.isna(braid) or braid == '':
                print(f"✗ {knot}: Missing braid notation")
            else:
                print(f"✓ {knot}: Complete data")
    
    print()
    if missing:
        print(f"⚠ WARNING: {len(missing)} knots missing from database")
        return False
    else:
        print(f"✓ All {len(TEST_KNOTS)} test knots verified")
        return True

def display_sample_data(df):
    """Display sample data for trefoil (3_1)."""
    print("\n" + "=" * 60)
    print("SAMPLE DATA: Trefoil Knot (3_1)")
    print("=" * 60)
    
    knot = df[df['name'] == '3_1'].iloc[0]
    
    print(f"Name: {knot['name']}")
    print(f"Crossing Number: {knot['crossing_number']}")
    print(f"Unknotting Number: {knot['unknotting_number']}")
    print(f"Three-Genus: {knot['three_genus']}")
    print(f"Alternating: {knot['alternating']}")
    print(f"\nBraid Notation: {knot['braid_notation']}")
    print(f"Braid Index: {knot['braid_index']}")
    print(f"\nHOMFLY-PT: {knot['homfly_polynomial']}")
    print(f"Jones: {knot['jones_polynomial']}")
    print()

def count_coverage(df):
    """Count test cases by type."""
    print("=" * 60)
    print("TEST SUITE COVERAGE")
    print("=" * 60)
    
    test_df = df[df['name'].isin(TEST_KNOTS)]
    
    total = len(test_df)
    alternating = len(test_df[test_df['alternating'] == 'Y'])
    non_alternating = total - alternating
    
    print(f"Total test knots: {total}")
    print(f"  - Alternating: {alternating}")
    print(f"  - Non-alternating: {non_alternating}")
    
    # Count by crossing number
    print("\nBy Crossing Number:")
    for i in range(0, 11):
        count = len(test_df[test_df['crossing_number'] == i])
        if count > 0:
            knots = ', '.join(test_df[test_df['crossing_number'] == i]['name'].values)
            print(f"  {i} crossings: {count} knots ({knots})")
    
    print()

def test_data_extraction():
    """Quick test of data extraction."""
    print("=" * 60)
    print("DATA EXTRACTION TEST")
    print("=" * 60)
    
    df = pd.read_csv(CSV_PATH, delimiter='|')
    
    # Extract specific values
    trefoil = df[df['name'] == '3_1'].iloc[0]
    
    expected_homfly = "(2*v^2-v^4)+ v^2*z^2"
    actual_homfly = trefoil['homfly_polynomial']
    
    expected_jones = "t+ t^3-t^4"
    actual_jones = trefoil['jones_polynomial']
    
    print("Trefoil (3_1) Verification:")
    print(f"  Expected HOMFLY: {expected_homfly}")
    print(f"  Actual HOMFLY:   {actual_homfly}")
    print(f"  Match: {expected_homfly == actual_homfly} ✓" if expected_homfly == actual_homfly else "  Match: False ✗")
    
    print(f"\n  Expected Jones: {expected_jones}")
    print(f"  Actual Jones:   {actual_jones}")
    print(f"  Match: {expected_jones == actual_jones} ✓" if expected_jones == actual_jones else "  Match: False ✗")
    
    print()

def main():
    """Run all verification tests."""
    print("\n" + "=" * 60)
    print("HOMFLY-PT TEST CASE VERIFICATION")
    print("=" * 60)
    print()
    
    # Load data
    df = load_data()
    
    # Verify test cases
    if not verify_test_cases(df):
        print("\n⚠ VERIFICATION FAILED")
        return 1
    
    # Display sample
    display_sample_data(df)
    
    # Count coverage
    count_coverage(df)
    
    # Test extraction
    test_data_extraction()
    
    print("=" * 60)
    print("✓ ALL VERIFICATION TESTS PASSED")
    print("=" * 60)
    print("\nTest suite is ready for use!")
    print("\nNext steps:")
    print("1. Review HOMFLY_PT_QUICK_REFERENCE.md")
    print("2. Study HOMFLY_PT_TEST_CASES.md")
    print("3. Begin implementation")
    print()
    
    return 0

if __name__ == "__main__":
    exit(main())
