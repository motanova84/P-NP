"""
Logarithmic Spiral Implementation
===================================

This module implements the logarithmic spiral equation:
    a = exp(θ × c₀)

where c₀ is a scale constant that can be derived from either:
1. κ_Π: c₀ = log(κ_Π) / (2π) ≈ 0.150
2. φ (golden ratio): c₀ = log(φ) / π ≈ 0.153

The spiral connects:
• Origin (θ=0, a=1)
• Infinity (θ→∞, a→∞)
• Passes through a = κ_Π when θ = log(κ_Π)/c₀

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import math
from typing import Tuple, List
from enum import Enum

from constants import KAPPA_PI, GOLDEN_RATIO, C_0_KAPPA, C_0_PHI


class SpiralVariant(Enum):
    """Variants of the logarithmic spiral based on c₀"""
    KAPPA = "kappa"  # c₀ = log(κ_Π) / (2π)
    PHI = "phi"      # c₀ = log(φ) / π


def get_c0(variant: SpiralVariant = SpiralVariant.KAPPA) -> float:
    """
    Get the scale constant c₀ for the specified spiral variant.
    
    Args:
        variant: Which variant to use (KAPPA or PHI)
        
    Returns:
        The c₀ scale constant
    """
    if variant == SpiralVariant.KAPPA:
        return C_0_KAPPA
    elif variant == SpiralVariant.PHI:
        return C_0_PHI
    else:
        raise ValueError(f"Unknown spiral variant: {variant}")


def spiral_radius(theta: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> float:
    """
    Calculate radius a in the logarithmic spiral: a = exp(θ × c₀)
    
    Args:
        theta: Angle parameter (in radians)
        variant: Which c₀ variant to use
        
    Returns:
        Radius a at the given angle
        
    Examples:
        >>> spiral_radius(0)  # At origin
        1.0
        >>> spiral_radius(theta_at_kappa())  # At κ_Π
        ≈ 2.5773
    """
    c0 = get_c0(variant)
    return math.exp(theta * c0)


def spiral_angle(radius: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> float:
    """
    Calculate angle θ given radius a: θ = log(a) / c₀
    
    Args:
        radius: Radius a (must be > 0)
        variant: Which c₀ variant to use
        
    Returns:
        Angle θ corresponding to the given radius
        
    Raises:
        ValueError: If radius <= 0
    """
    if radius <= 0:
        raise ValueError("Radius must be positive")
    
    c0 = get_c0(variant)
    return math.log(radius) / c0


def theta_at_kappa(variant: SpiralVariant = SpiralVariant.KAPPA) -> float:
    """
    Calculate the angle θ where the spiral passes through a = κ_Π.
    
    θ = log(κ_Π) / c₀
    
    Args:
        variant: Which c₀ variant to use
        
    Returns:
        Angle where a = κ_Π
    """
    return spiral_angle(KAPPA_PI, variant)


def spiral_coordinates(theta: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> Tuple[float, float]:
    """
    Calculate Cartesian coordinates (x, y) from polar coordinates (θ, a).
    
    x = a × cos(θ)
    y = a × sin(θ)
    
    where a = exp(θ × c₀)
    
    Args:
        theta: Angle parameter (in radians)
        variant: Which c₀ variant to use
        
    Returns:
        Tuple (x, y) of Cartesian coordinates
    """
    a = spiral_radius(theta, variant)
    x = a * math.cos(theta)
    y = a * math.sin(theta)
    return (x, y)


def spiral_points(num_points: int, 
                  theta_max: float = 4 * math.pi,
                  variant: SpiralVariant = SpiralVariant.KAPPA) -> List[Tuple[float, float, float]]:
    """
    Generate a list of points along the logarithmic spiral.
    
    Args:
        num_points: Number of points to generate (must be >= 0)
        theta_max: Maximum angle to sample (default: 4π, two full rotations)
        variant: Which c₀ variant to use
        
    Returns:
        List of tuples (θ, x, y) representing points on the spiral
        
    Raises:
        ValueError: If num_points < 0
    """
    if num_points < 0:
        raise ValueError("num_points must be non-negative")
    
    if num_points == 0:
        return []
    
    points = []
    for i in range(num_points):
        theta = (theta_max * i) / max(num_points - 1, 1)
        x, y = spiral_coordinates(theta, variant)
        points.append((theta, x, y))
    
    return points


def spiral_arc_length(theta_start: float, 
                      theta_end: float, 
                      variant: SpiralVariant = SpiralVariant.KAPPA) -> float:
    """
    Calculate approximate arc length along the spiral between two angles.
    
    For a logarithmic spiral a = exp(c₀θ), the arc length from θ₁ to θ₂ is:
    L = (a₂ - a₁) × √(1 + 1/c₀²) / c₀
    
    Args:
        theta_start: Starting angle
        theta_end: Ending angle
        variant: Which c₀ variant to use
        
    Returns:
        Approximate arc length
    """
    c0 = get_c0(variant)
    a1 = spiral_radius(theta_start, variant)
    a2 = spiral_radius(theta_end, variant)
    
    # Arc length formula for logarithmic spiral
    scaling_factor = math.sqrt(1 + 1 / (c0 ** 2))
    return abs(a2 - a1) * scaling_factor / c0


def verify_spiral_properties(variant: SpiralVariant = SpiralVariant.KAPPA) -> dict:
    """
    Verify key properties of the logarithmic spiral.
    
    Args:
        variant: Which c₀ variant to verify
        
    Returns:
        Dictionary with verification results
    """
    c0 = get_c0(variant)
    
    results = {
        'variant': variant.value,
        'c0': c0,
        'c0_expected_kappa': C_0_KAPPA,
        'c0_expected_phi': C_0_PHI,
    }
    
    # Property 1: Origin (θ=0, a=1)
    a_at_origin = spiral_radius(0, variant)
    results['a_at_origin'] = a_at_origin
    results['origin_correct'] = abs(a_at_origin - 1.0) < 1e-10
    
    # Property 2: Passes through a = κ_Π at specific θ
    theta_kappa = theta_at_kappa(variant)
    a_at_theta_kappa = spiral_radius(theta_kappa, variant)
    results['theta_at_kappa'] = theta_kappa
    results['a_at_theta_kappa'] = a_at_theta_kappa
    results['kappa_crossing_correct'] = abs(a_at_theta_kappa - KAPPA_PI) < 1e-6
    
    # Property 3: θ → ∞ implies a → ∞
    large_theta = 100
    a_large = spiral_radius(large_theta, variant)
    results['a_at_large_theta'] = a_large
    results['grows_to_infinity'] = a_large > 1000
    
    # Property 4: Verify inverse relationship
    test_a = 5.0
    theta_from_a = spiral_angle(test_a, variant)
    a_recovered = spiral_radius(theta_from_a, variant)
    results['inverse_correct'] = abs(a_recovered - test_a) < 1e-10
    
    return results


# ========== MODULE INITIALIZATION ==========

if __name__ == "__main__":
    print("=" * 70)
    print("Logarithmic Spiral: a = exp(θ × c₀)")
    print("=" * 70)
    print()
    
    # Test both variants
    for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
        print(f"\n{'='*70}")
        print(f"Variant: {variant.value.upper()}")
        print(f"{'='*70}")
        
        c0 = get_c0(variant)
        print(f"\nScale constant c₀ = {c0:.6f}")
        
        if variant == SpiralVariant.KAPPA:
            print(f"  Derived from: log(κ_Π) / (2π)")
            print(f"  κ_Π = {KAPPA_PI}")
            expected = math.log(KAPPA_PI) / (2 * math.pi)
            print(f"  Expected c₀ ≈ {expected:.6f}")
        else:
            print(f"  Derived from: log(φ) / π")
            print(f"  φ = {GOLDEN_RATIO:.6f}")
            expected = math.log(GOLDEN_RATIO) / math.pi
            print(f"  Expected c₀ ≈ {expected:.6f}")
        
        print(f"\nKey Points:")
        print(f"  • Origin (θ=0): a = {spiral_radius(0, variant):.6f}")
        
        theta_k = theta_at_kappa(variant)
        print(f"  • Passes through κ_Π at θ = {theta_k:.6f} rad")
        print(f"    a(θ) = {spiral_radius(theta_k, variant):.6f} ≈ κ_Π")
        
        # Show a few sample points
        print(f"\nSample Points (θ, a, x, y):")
        for theta in [0, math.pi/2, math.pi, 2*math.pi]:
            a = spiral_radius(theta, variant)
            x, y = spiral_coordinates(theta, variant)
            print(f"  θ = {theta:6.3f} rad → a = {a:8.4f}, x = {x:8.4f}, y = {y:8.4f}")
        
        # Verify properties
        print(f"\nVerification:")
        results = verify_spiral_properties(variant)
        print(f"  ✓ Origin correct: {results['origin_correct']}")
        print(f"  ✓ κ_Π crossing correct: {results['kappa_crossing_correct']}")
        print(f"  ✓ Grows to infinity: {results['grows_to_infinity']}")
        print(f"  ✓ Inverse correct: {results['inverse_correct']}")
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
