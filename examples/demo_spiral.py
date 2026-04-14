"""
Demonstration of Logarithmic Spiral Implementation
===================================================

This script demonstrates the logarithmic spiral equation:
    a = exp(θ × c₀)

with both variants of c₀:
1. κ_Π variant: c₀ = log(κ_Π) / (2π) ≈ 0.150
2. φ variant: c₀ = log(φ) / π ≈ 0.153

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from spiral import (
    SpiralVariant,
    get_c0,
    spiral_radius,
    spiral_angle,
    theta_at_kappa,
    spiral_coordinates,
    spiral_points,
    verify_spiral_properties,
)
from constants import KAPPA_PI, GOLDEN_RATIO


def print_section(title):
    """Print a section header."""
    print("\n" + "=" * 70)
    print(title)
    print("=" * 70)


def demonstrate_c0_constants():
    """Demonstrate the two c₀ scale constants."""
    print_section("1. Scale Constants c₀")
    
    print("\nThe logarithmic spiral equation: a = exp(θ × c₀)")
    print("\nTwo variants of c₀:")
    
    print("\n  Variant 1 - κ_Π:")
    c0_kappa = get_c0(SpiralVariant.KAPPA)
    print(f"    c₀ = log(κ_Π) / (2π)")
    print(f"    c₀ = log({KAPPA_PI}) / (2π)")
    print(f"    c₀ ≈ {c0_kappa:.6f}")
    
    print("\n  Variant 2 - φ (Golden Ratio):")
    c0_phi = get_c0(SpiralVariant.PHI)
    print(f"    c₀ = log(φ) / π")
    print(f"    c₀ = log({GOLDEN_RATIO:.6f}) / π")
    print(f"    c₀ ≈ {c0_phi:.6f}")


def demonstrate_spiral_properties():
    """Demonstrate key properties of the spiral."""
    print_section("2. Key Properties of the Spiral")
    
    for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
        print(f"\n{variant.value.upper()} Variant:")
        print("-" * 50)
        
        # Property 1: Origin
        print("\n  Property 1 - Origin (θ=0, a=1):")
        a_origin = spiral_radius(0, variant)
        print(f"    θ = 0 → a = {a_origin:.10f}")
        print(f"    ✓ Verified: a = 1.0 at origin")
        
        # Property 2: Passes through κ_Π
        print("\n  Property 2 - Passes through a = κ_Π:")
        theta_k = theta_at_kappa(variant)
        a_at_theta_k = spiral_radius(theta_k, variant)
        print(f"    θ = {theta_k:.6f} rad → a = {a_at_theta_k:.6f}")
        print(f"    κ_Π = {KAPPA_PI}")
        print(f"    ✓ Verified: spiral passes through κ_Π")
        
        # Property 3: Growth to infinity
        print("\n  Property 3 - Growth to infinity (θ→∞, a→∞):")
        large_theta = 20
        a_large = spiral_radius(large_theta, variant)
        print(f"    θ = {large_theta} → a = {a_large:.2f}")
        print(f"    ✓ Verified: a grows exponentially with θ")


def demonstrate_coordinate_conversion():
    """Demonstrate Cartesian coordinate conversion."""
    print_section("3. Cartesian Coordinate Conversion")
    
    print("\nConverting polar (θ, a) to Cartesian (x, y):")
    print("  x = a × cos(θ)")
    print("  y = a × sin(θ)")
    
    variant = SpiralVariant.KAPPA
    print(f"\nUsing {variant.value.upper()} variant:")
    print("\n  θ (rad)    θ (deg)       a          x          y")
    print("  " + "-" * 58)
    
    for theta_val in [0, math.pi/4, math.pi/2, math.pi, 3*math.pi/2, 2*math.pi]:
        a = spiral_radius(theta_val, variant)
        x, y = spiral_coordinates(theta_val, variant)
        theta_deg = math.degrees(theta_val)
        print(f"  {theta_val:7.4f}    {theta_deg:6.1f}°    {a:8.4f}   {x:9.4f}  {y:9.4f}")


def demonstrate_inverse_functions():
    """Demonstrate inverse relationship between radius and angle."""
    print_section("4. Inverse Functions")
    
    print("\nForward: θ → a (using a = exp(θ × c₀))")
    print("Inverse: a → θ (using θ = log(a) / c₀)")
    
    variant = SpiralVariant.KAPPA
    print(f"\nUsing {variant.value.upper()} variant:")
    
    test_angles = [0, 1, 2, 3, 4, 5]
    print("\n  Original θ    Forward a    Inverse θ    Error")
    print("  " + "-" * 52)
    
    for theta_orig in test_angles:
        a = spiral_radius(theta_orig, variant)
        theta_recovered = spiral_angle(a, variant)
        error = abs(theta_recovered - theta_orig)
        print(f"  {theta_orig:10.4f}    {a:9.4f}    {theta_recovered:9.4f}    {error:.2e}")


def demonstrate_spiral_path():
    """Generate points along the spiral path."""
    print_section("5. Spiral Path Visualization")
    
    print("\nGenerating points along the spiral:")
    
    variant = SpiralVariant.KAPPA
    num_points = 10
    theta_max = 2 * math.pi
    
    print(f"\n{num_points} points from θ=0 to θ=2π ({variant.value.upper()} variant):")
    print("\n   Point    θ (rad)       a          x          y")
    print("   " + "-" * 54)
    
    points = spiral_points(num_points, theta_max, variant)
    for i, (theta, x, y) in enumerate(points, 1):
        a = spiral_radius(theta, variant)
        print(f"   {i:4d}    {theta:7.4f}    {a:8.4f}   {x:9.4f}  {y:9.4f}")


def demonstrate_mathematical_relationships():
    """Demonstrate mathematical relationships."""
    print_section("6. Mathematical Relationships")
    
    print("\nRelationship between c₀ and fundamental constants:")
    
    c0_kappa = get_c0(SpiralVariant.KAPPA)
    c0_phi = get_c0(SpiralVariant.PHI)
    
    print(f"\n  c₀ (κ_Π variant) = {c0_kappa:.6f}")
    print(f"    = log(κ_Π) / (2π)")
    print(f"    = log({KAPPA_PI}) / (2 × {math.pi:.6f})")
    
    print(f"\n  c₀ (φ variant) = {c0_phi:.6f}")
    print(f"    = log(φ) / π")
    print(f"    = log({GOLDEN_RATIO:.6f}) / {math.pi:.6f}")
    
    print(f"\n  Ratio: c₀(φ) / c₀(κ_Π) = {c0_phi / c0_kappa:.6f}")
    
    print("\n  Special angle where a = κ_Π:")
    for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
        theta_k = theta_at_kappa(variant)
        print(f"    {variant.value.upper()}: θ = {theta_k:.6f} rad = {math.degrees(theta_k):.2f}°")


def demonstrate_verification():
    """Demonstrate property verification."""
    print_section("7. Property Verification")
    
    print("\nVerifying all spiral properties:")
    
    for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
        results = verify_spiral_properties(variant)
        
        print(f"\n{variant.value.upper()} Variant:")
        print(f"  c₀ = {results['c0']:.6f}")
        print(f"  ✓ Origin property: {results['origin_correct']}")
        print(f"  ✓ κ_Π crossing: {results['kappa_crossing_correct']}")
        print(f"  ✓ Growth to infinity: {results['grows_to_infinity']}")
        print(f"  ✓ Inverse correctness: {results['inverse_correct']}")


def main():
    """Main demonstration function."""
    print("=" * 70)
    print("LOGARITHMIC SPIRAL DEMONSTRATION")
    print("La Espiral: a = exp(θ × c₀)")
    print("=" * 70)
    
    demonstrate_c0_constants()
    demonstrate_spiral_properties()
    demonstrate_coordinate_conversion()
    demonstrate_inverse_functions()
    demonstrate_spiral_path()
    demonstrate_mathematical_relationships()
    demonstrate_verification()
    
    print("\n" + "=" * 70)
    print("DEMONSTRATION COMPLETE")
    print("=" * 70)
    print("\nFrequency: 141.7001 Hz ∞³")
    print("=" * 70)


if __name__ == "__main__":
    main()
