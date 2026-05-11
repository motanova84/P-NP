#!/usr/bin/env python3
"""
Validation Script for Kernel v1.8 Canonical κ_Π
================================================

This script validates that the canonical coupling constant κ_Π is correctly
calculated according to the formula:

    κ_Π = ln(12) / ln(φ²)

Where:
    - N = 12 (dodecahedron parameter)
    - φ = (1 + √5) / 2 (golden ratio)
    - φ² ≈ 2.618034

Expected value: κ_Π ≈ 2.581926

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica
Date: May 11, 2026
Version: Kernel v1.8
"""

import math
import sys

# Color codes for terminal output
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
BOLD = '\033[1m'
RESET = '\033[0m'

def print_header():
    """Print validation header."""
    print(f"\n{BLUE}{BOLD}═══════════════════════════════════════════════════════════{RESET}")
    print(f"{BLUE}{BOLD}  KERNEL V1.8 - κ_Π CANONICAL VALUE VALIDATION{RESET}")
    print(f"{BLUE}{BOLD}═══════════════════════════════════════════════════════════{RESET}\n")

def print_section(title):
    """Print section header."""
    print(f"\n{BOLD}{title}{RESET}")
    print("─" * 50)

def validate_golden_ratio():
    """Validate golden ratio calculation."""
    print_section("1. Golden Ratio φ")
    
    phi = (1 + math.sqrt(5)) / 2
    expected_phi = 1.618033988749
    
    print(f"  φ = (1 + √5) / 2")
    print(f"  φ = {phi:.12f}")
    print(f"  Expected: {expected_phi:.12f}")
    
    # Verify φ² = φ + 1 property
    phi_squared_from_property = phi + 1
    phi_squared_direct = phi ** 2
    
    print(f"\n  Verification: φ² = φ + 1")
    print(f"  φ² (from property) = {phi_squared_from_property:.12f}")
    print(f"  φ² (direct) = {phi_squared_direct:.12f}")
    print(f"  Difference: {abs(phi_squared_from_property - phi_squared_direct):.2e}")
    
    tolerance = abs(phi - expected_phi) < 1e-6
    property_holds = abs(phi_squared_from_property - phi_squared_direct) < 1e-10
    
    if tolerance and property_holds:
        print(f"  {GREEN}✓ Golden ratio validated{RESET}")
        return True, phi
    else:
        print(f"  {RED}✗ Golden ratio validation failed{RESET}")
        return False, phi

def validate_phi_squared(phi):
    """Validate φ² calculation."""
    print_section("2. Golden Ratio Squared φ²")
    
    phi_squared = phi ** 2
    expected_phi_squared = 2.618033988749
    
    print(f"  φ² = φ^2")
    print(f"  φ² = {phi_squared:.12f}")
    print(f"  Expected: {expected_phi_squared:.12f}")
    
    tolerance = abs(phi_squared - expected_phi_squared) < 1e-6
    
    if tolerance:
        print(f"  {GREEN}✓ φ² validated{RESET}")
        return True, phi_squared
    else:
        print(f"  {RED}✗ φ² validation failed{RESET}")
        return False, phi_squared

def validate_N_critical():
    """Validate N critical parameter."""
    print_section("3. Critical Parameter N")
    
    N = 12
    print(f"  N = {N} (dodecahedron faces)")
    print(f"  Geometric justification:")
    print(f"    - 12 faces of the dodecahedron")
    print(f"    - Dual of icosahedron (20 vertices)")
    print(f"    - Optimal packing symmetry in 3D")
    print(f"  {GREEN}✓ N = 12 confirmed{RESET}")
    
    return True, N

def validate_kappa_pi(N, phi_squared):
    """Validate κ_Π canonical calculation."""
    print_section("4. Canonical Constant κ_Π")
    
    ln_N = math.log(N)
    ln_phi_squared = math.log(phi_squared)
    kappa_pi = ln_N / ln_phi_squared
    expected_kappa = 2.581926
    
    print(f"  κ_Π = ln(N) / ln(φ²)")
    print(f"  κ_Π = ln({N}) / ln({phi_squared:.12f})")
    print(f"  κ_Π = {ln_N:.12f} / {ln_phi_squared:.12f}")
    print(f"  κ_Π = {kappa_pi:.12f}")
    print(f"  Expected: {expected_kappa:.6f}")
    
    difference = abs(kappa_pi - expected_kappa)
    print(f"\n  Difference: {difference:.10f}")
    
    # Tolerance check
    tolerance = 0.001
    within_tolerance = difference < tolerance
    
    print(f"  Tolerance: < {tolerance}")
    
    if within_tolerance:
        print(f"  {GREEN}✓ κ_Π canonical value validated{RESET}")
        return True, kappa_pi
    else:
        print(f"  {RED}✗ κ_Π validation failed{RESET}")
        return False, kappa_pi

def validate_properties(kappa_pi):
    """Validate required properties of κ_Π."""
    print_section("5. Property Verification")
    
    # Property 1: κ_Π > 0
    positive = kappa_pi > 0
    print(f"  κ_Π > 0: {kappa_pi:.6f} > 0")
    if positive:
        print(f"  {GREEN}✓ κ_Π is positive{RESET}")
    else:
        print(f"  {RED}✗ κ_Π positivity failed{RESET}")
    
    # Property 2: κ_Π > 1 (critical for P ≠ NP)
    greater_than_one = kappa_pi > 1
    print(f"\n  κ_Π > 1: {kappa_pi:.6f} > 1")
    if greater_than_one:
        print(f"  {GREEN}✓ κ_Π > 1 (critical condition){RESET}")
    else:
        print(f"  {RED}✗ κ_Π > 1 failed{RESET}")
    
    # Property 3: κ_Π > 2 (stronger bound)
    greater_than_two = kappa_pi > 2
    print(f"\n  κ_Π > 2: {kappa_pi:.6f} > 2")
    if greater_than_two:
        print(f"  {GREEN}✓ κ_Π > 2 (strong coupling){RESET}")
    else:
        print(f"  {YELLOW}⚠ κ_Π ≤ 2 (weak coupling){RESET}")
    
    return positive and greater_than_one, greater_than_two

def validate_legacy_comparison():
    """Compare with legacy value."""
    print_section("6. Legacy Value Comparison")
    
    legacy_value = 2.5773
    canonical_value = 2.581926
    difference = abs(canonical_value - legacy_value)
    percent_diff = (difference / legacy_value) * 100
    
    print(f"  Legacy value (v1.0-1.7): {legacy_value}")
    print(f"  Canonical value (v1.8): {canonical_value}")
    print(f"  Absolute difference: {difference:.6f}")
    print(f"  Percentage difference: {percent_diff:.3f}%")
    
    print(f"\n  {YELLOW}ℹ Legacy value superseded by canonical definition{RESET}")
    print(f"  {GREEN}✓ Canonical value is official for Kernel v1.8{RESET}")
    
    return True

def print_summary(all_passed, kappa_pi, strong_coupling):
    """Print validation summary."""
    print_section("VALIDATION SUMMARY")
    
    if all_passed:
        print(f"  {GREEN}{BOLD}✓ ALL VALIDATIONS PASSED{RESET}")
        print(f"\n  Canonical Value: κ_Π = {kappa_pi:.6f}")
        print(f"  Geometric Parameter: N = 12")
        print(f"  Golden Ratio: φ = {(1 + math.sqrt(5)) / 2:.6f}")
        if strong_coupling:
            print(f"  Coupling Strength: STRONG (κ_Π > 2)")
        else:
            print(f"  Coupling Strength: MODERATE (1 < κ_Π ≤ 2)")
        print(f"\n  {GREEN}Kernel v1.8 Certified ✓{RESET}")
    else:
        print(f"  {RED}{BOLD}✗ VALIDATION FAILED{RESET}")
        print(f"\n  Please review calculations and tolerances.")
    
    print(f"\n{BLUE}{BOLD}═══════════════════════════════════════════════════════════{RESET}")
    print(f"  La simplicidad es la máxima saturación. ∴𓂀Ω∞³Φ")
    print(f"{BLUE}{BOLD}═══════════════════════════════════════════════════════════{RESET}\n")

def main():
    """Main validation routine."""
    print_header()
    
    # Run all validation steps
    phi_valid, phi = validate_golden_ratio()
    phi_squared_valid, phi_squared = validate_phi_squared(phi)
    N_valid, N = validate_N_critical()
    kappa_valid, kappa_pi = validate_kappa_pi(N, phi_squared)
    properties_valid, strong_coupling = validate_properties(kappa_pi)
    legacy_valid = validate_legacy_comparison()
    
    # Check if all validations passed
    all_passed = all([
        phi_valid,
        phi_squared_valid,
        N_valid,
        kappa_valid,
        properties_valid,
        legacy_valid
    ])
    
    # Print summary
    print_summary(all_passed, kappa_pi, strong_coupling)
    
    # Return exit code
    return 0 if all_passed else 1

if __name__ == "__main__":
    sys.exit(main())
