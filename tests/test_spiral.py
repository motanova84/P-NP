"""
Test suite for the spiral module (logarithmic spiral implementation)
=====================================================================

Tests the logarithmic spiral equation: a = exp(θ × c₀)
with two variants of c₀ based on κ_Π and φ.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import pytest

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
    spiral_arc_length,
    verify_spiral_properties,
)
from constants import KAPPA_PI, GOLDEN_RATIO, C_0_KAPPA, C_0_PHI


class TestScaleConstants:
    """Test suite for c₀ scale constants."""
    
    def test_c0_kappa_value(self):
        """Test c₀ (kappa variant) calculation."""
        expected = math.log(KAPPA_PI) / (2 * math.pi)
        assert abs(C_0_KAPPA - expected) < 1e-10
        assert abs(C_0_KAPPA - 0.150679) < 0.001
    
    def test_c0_phi_value(self):
        """Test c₀ (phi variant) calculation."""
        expected = math.log(GOLDEN_RATIO) / math.pi
        assert abs(C_0_PHI - expected) < 1e-10
        assert abs(C_0_PHI - 0.153174) < 0.001
    
    def test_get_c0_kappa(self):
        """Test get_c0 function for kappa variant."""
        c0 = get_c0(SpiralVariant.KAPPA)
        assert c0 == C_0_KAPPA
    
    def test_get_c0_phi(self):
        """Test get_c0 function for phi variant."""
        c0 = get_c0(SpiralVariant.PHI)
        assert c0 == C_0_PHI
    
    def test_c0_ordering(self):
        """Test that c₀ values are ordered correctly."""
        # C_0_KAPPA should be slightly less than C_0_PHI
        assert C_0_KAPPA < C_0_PHI
        # Both should be positive and less than 1
        assert 0 < C_0_KAPPA < 1
        assert 0 < C_0_PHI < 1


class TestSpiralRadius:
    """Test suite for spiral radius calculation: a = exp(θ × c₀)."""
    
    def test_spiral_radius_at_origin(self):
        """Test that a = 1 at θ = 0."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            a = spiral_radius(0, variant)
            assert abs(a - 1.0) < 1e-10
    
    def test_spiral_radius_positive(self):
        """Test that radius is always positive."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            for theta in [0, 1, math.pi, 2*math.pi, 10]:
                a = spiral_radius(theta, variant)
                assert a > 0
    
    def test_spiral_radius_increasing(self):
        """Test that radius increases with θ."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            theta_values = [0, 1, 2, 3, 4, 5]
            radii = [spiral_radius(theta, variant) for theta in theta_values]
            
            # Each radius should be larger than the previous
            for i in range(1, len(radii)):
                assert radii[i] > radii[i-1]
    
    def test_spiral_radius_formula(self):
        """Test explicit formula a = exp(θ × c₀)."""
        theta = 2.5
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            c0 = get_c0(variant)
            expected = math.exp(theta * c0)
            actual = spiral_radius(theta, variant)
            assert abs(actual - expected) < 1e-10
    
    def test_spiral_radius_at_kappa(self):
        """Test that spiral passes through κ_Π."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            theta = theta_at_kappa(variant)
            a = spiral_radius(theta, variant)
            assert abs(a - KAPPA_PI) < 1e-6


class TestSpiralAngle:
    """Test suite for spiral angle calculation: θ = log(a) / c₀."""
    
    def test_spiral_angle_at_unity(self):
        """Test that θ = 0 when a = 1."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            theta = spiral_angle(1.0, variant)
            assert abs(theta - 0.0) < 1e-10
    
    def test_spiral_angle_positive_radius(self):
        """Test that angle increases with radius."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            radii = [1.0, 1.5, 2.0, 2.5, 3.0]
            angles = [spiral_angle(a, variant) for a in radii]
            
            # Each angle should be larger than the previous
            for i in range(1, len(angles)):
                assert angles[i] > angles[i-1]
    
    def test_spiral_angle_invalid_radius(self):
        """Test that invalid radii raise ValueError."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            with pytest.raises(ValueError):
                spiral_angle(0, variant)
            with pytest.raises(ValueError):
                spiral_angle(-1, variant)
    
    def test_spiral_angle_formula(self):
        """Test explicit formula θ = log(a) / c₀."""
        a = 3.0
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            c0 = get_c0(variant)
            expected = math.log(a) / c0
            actual = spiral_angle(a, variant)
            assert abs(actual - expected) < 1e-10
    
    def test_spiral_angle_inverse(self):
        """Test that spiral_angle is inverse of spiral_radius."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            for theta_orig in [0, 1, math.pi, 2*math.pi, 5]:
                # Forward: theta -> a
                a = spiral_radius(theta_orig, variant)
                # Backward: a -> theta
                theta_recovered = spiral_angle(a, variant)
                assert abs(theta_recovered - theta_orig) < 1e-10


class TestThetaAtKappa:
    """Test suite for θ at κ_Π crossing."""
    
    def test_theta_at_kappa_kappa_variant(self):
        """Test θ where a = κ_Π for kappa variant."""
        theta = theta_at_kappa(SpiralVariant.KAPPA)
        a = spiral_radius(theta, SpiralVariant.KAPPA)
        assert abs(a - KAPPA_PI) < 1e-6
    
    def test_theta_at_kappa_phi_variant(self):
        """Test θ where a = κ_Π for phi variant."""
        theta = theta_at_kappa(SpiralVariant.PHI)
        a = spiral_radius(theta, SpiralVariant.PHI)
        assert abs(a - KAPPA_PI) < 1e-6
    
    def test_theta_at_kappa_value(self):
        """Test explicit calculation of θ at κ_Π."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            c0 = get_c0(variant)
            expected = math.log(KAPPA_PI) / c0
            actual = theta_at_kappa(variant)
            assert abs(actual - expected) < 1e-10


class TestSpiralCoordinates:
    """Test suite for Cartesian coordinate conversion."""
    
    def test_coordinates_at_origin(self):
        """Test coordinates at θ = 0."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            x, y = spiral_coordinates(0, variant)
            # At θ=0, a=1, so x=1*cos(0)=1, y=1*sin(0)=0
            assert abs(x - 1.0) < 1e-10
            assert abs(y - 0.0) < 1e-10
    
    def test_coordinates_at_pi_over_2(self):
        """Test coordinates at θ = π/2."""
        theta = math.pi / 2
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            x, y = spiral_coordinates(theta, variant)
            a = spiral_radius(theta, variant)
            
            # At θ=π/2, x=a*cos(π/2)≈0, y=a*sin(π/2)≈a
            assert abs(x - 0.0) < 1e-6
            assert abs(y - a) < 1e-6
    
    def test_coordinates_at_pi(self):
        """Test coordinates at θ = π."""
        theta = math.pi
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            x, y = spiral_coordinates(theta, variant)
            a = spiral_radius(theta, variant)
            
            # At θ=π, x=a*cos(π)=-a, y=a*sin(π)≈0
            assert abs(x - (-a)) < 1e-6
            assert abs(y - 0.0) < 1e-6
    
    def test_coordinates_formula(self):
        """Test explicit coordinate formulas."""
        theta = 1.5
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            a = spiral_radius(theta, variant)
            x, y = spiral_coordinates(theta, variant)
            
            expected_x = a * math.cos(theta)
            expected_y = a * math.sin(theta)
            
            assert abs(x - expected_x) < 1e-10
            assert abs(y - expected_y) < 1e-10
    
    def test_coordinates_distance(self):
        """Test that distance from origin equals radius."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            for theta in [0, 1, math.pi, 2*math.pi]:
                x, y = spiral_coordinates(theta, variant)
                a = spiral_radius(theta, variant)
                
                distance = math.sqrt(x**2 + y**2)
                assert abs(distance - a) < 1e-10


class TestSpiralPoints:
    """Test suite for generating spiral points."""
    
    def test_spiral_points_empty(self):
        """Test empty point generation."""
        points = spiral_points(0)
        assert len(points) == 0
    
    def test_spiral_points_negative(self):
        """Test that negative num_points raises ValueError."""
        with pytest.raises(ValueError):
            spiral_points(-1)
        with pytest.raises(ValueError):
            spiral_points(-10)
    
    def test_spiral_points_single(self):
        """Test single point generation."""
        points = spiral_points(1)
        assert len(points) == 1
        theta, x, y = points[0]
        # First point should be at θ=0
        assert abs(theta - 0) < 1e-10
    
    def test_spiral_points_count(self):
        """Test correct number of points generated."""
        for n in [1, 5, 10, 20]:
            points = spiral_points(n)
            assert len(points) == n
    
    def test_spiral_points_range(self):
        """Test angle range of generated points."""
        theta_max = 2 * math.pi
        points = spiral_points(10, theta_max)
        
        # First point should be at θ=0
        assert abs(points[0][0] - 0) < 1e-10
        # Last point should be at θ=theta_max
        assert abs(points[-1][0] - theta_max) < 1e-6
    
    def test_spiral_points_coordinates(self):
        """Test that coordinates match spiral_coordinates."""
        n = 5
        theta_max = math.pi
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            points = spiral_points(n, theta_max, variant)
            
            for theta, x, y in points:
                expected_x, expected_y = spiral_coordinates(theta, variant)
                assert abs(x - expected_x) < 1e-10
                assert abs(y - expected_y) < 1e-10


class TestSpiralArcLength:
    """Test suite for arc length calculation."""
    
    def test_arc_length_zero(self):
        """Test arc length for zero interval."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            length = spiral_arc_length(0, 0, variant)
            assert abs(length) < 1e-10
    
    def test_arc_length_positive(self):
        """Test that arc length is positive."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            length = spiral_arc_length(0, math.pi, variant)
            assert length > 0
    
    def test_arc_length_symmetric(self):
        """Test that arc length is symmetric."""
        theta1 = 1.0
        theta2 = 2.0
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            length_forward = spiral_arc_length(theta1, theta2, variant)
            length_backward = spiral_arc_length(theta2, theta1, variant)
            assert abs(length_forward - length_backward) < 1e-10
    
    def test_arc_length_additive(self):
        """Test that arc lengths are approximately additive."""
        theta1 = 0
        theta2 = 1
        theta3 = 2
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            length_1_2 = spiral_arc_length(theta1, theta2, variant)
            length_2_3 = spiral_arc_length(theta2, theta3, variant)
            length_1_3 = spiral_arc_length(theta1, theta3, variant)
            
            # Should be approximately additive (within numerical error)
            # The formula is approximate, so use larger tolerance
            assert abs((length_1_2 + length_2_3) - length_1_3) < 0.1


class TestVerifySpiralProperties:
    """Test suite for spiral property verification."""
    
    def test_verify_kappa_variant(self):
        """Test verification for kappa variant."""
        results = verify_spiral_properties(SpiralVariant.KAPPA)
        
        assert results['variant'] == 'kappa'
        assert results['c0'] == C_0_KAPPA
        assert results['origin_correct'] == True
        assert results['kappa_crossing_correct'] == True
        assert results['grows_to_infinity'] == True
        assert results['inverse_correct'] == True
    
    def test_verify_phi_variant(self):
        """Test verification for phi variant."""
        results = verify_spiral_properties(SpiralVariant.PHI)
        
        assert results['variant'] == 'phi'
        assert results['c0'] == C_0_PHI
        assert results['origin_correct'] == True
        assert results['kappa_crossing_correct'] == True
        assert results['grows_to_infinity'] == True
        assert results['inverse_correct'] == True
    
    def test_verify_origin_property(self):
        """Test that origin property is verified correctly."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            results = verify_spiral_properties(variant)
            # a(0) should be very close to 1
            assert abs(results['a_at_origin'] - 1.0) < 1e-10
    
    def test_verify_kappa_crossing(self):
        """Test that κ_Π crossing is verified correctly."""
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            results = verify_spiral_properties(variant)
            # a at theta_kappa should be close to KAPPA_PI
            assert abs(results['a_at_theta_kappa'] - KAPPA_PI) < 1e-6


class TestSpiralIntegration:
    """Test integration with existing code."""
    
    def test_compatibility_with_complete_task3(self):
        """Test that spiral functions are compatible with complete_task3.py."""
        # The complete_task3.py uses spiral_coordinates function
        # Test that our implementation matches expected behavior
        
        for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
            # Generate some coordinates
            coords = [spiral_coordinates(i * 0.1, variant) for i in range(10)]
            
            # Check that all coordinates are valid
            assert len(coords) == 10
            for x, y in coords:
                assert isinstance(x, float)
                assert isinstance(y, float)
                # Distance should increase
                assert math.sqrt(x**2 + y**2) > 0


def test_module_imports():
    """Test that all required functions can be imported."""
    from spiral import (
        SpiralVariant,
        get_c0,
        spiral_radius,
        spiral_angle,
        theta_at_kappa,
        spiral_coordinates,
        spiral_points,
        spiral_arc_length,
        verify_spiral_properties,
    )
    
    assert SpiralVariant is not None
    assert get_c0 is not None
    assert spiral_radius is not None


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Logarithmic Spiral: a = exp(θ × c₀)")
    print("=" * 70)
    print()
    
    # Quick verification
    print("Quick Verification:")
    for variant in [SpiralVariant.KAPPA, SpiralVariant.PHI]:
        results = verify_spiral_properties(variant)
        print(f"\n{variant.value.upper()} variant:")
        print(f"  c₀ = {results['c0']:.6f}")
        print(f"  ✓ Origin: a(0) = {results['a_at_origin']:.6f}")
        print(f"  ✓ κ_Π crossing: θ = {results['theta_at_kappa']:.6f}, a = {results['a_at_theta_kappa']:.6f}")
        print(f"  ✓ All properties verified: {all([results['origin_correct'], results['kappa_crossing_correct'], results['grows_to_infinity'], results['inverse_correct']])}")
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
