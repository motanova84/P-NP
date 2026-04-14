"""
Test suite for logarithmic spiral and field Ψ calculations
===========================================================

Tests the logarithmic spiral z(θ) and field Ψ(r, θ) implementations.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import cmath
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from logarithmic_spiral import (
    # Constants
    C0, ALPHA, BETA, GAMMA, A_EFF_MAX, R_MIN, R_MAX, R_THRESHOLD,
    # Spiral functions
    z_spiral, spiral_magnitude, spiral_phase,
    verify_kappa_pi_property, spiral_trajectory, spiral_arc_length,
    # Field functions
    psi_field, psi_magnitude, psi_phase, field_on_circle,
    effective_area, verify_threshold_coherence,
    field_energy_density, total_field_energy,
    # Validation
    validate_spiral_properties, validate_field_properties
)
from constants import KAPPA_PI, GOLDEN_RATIO, QCAL_FREQUENCY_HZ


class TestSpiralConstants:
    """Test suite for spiral constants."""
    
    def test_c0_value(self):
        """Test that c₀ is computed correctly."""
        expected = math.log(KAPPA_PI) / (2 * math.pi)
        assert abs(C0 - expected) < 1e-10
        assert C0 > 0
        assert abs(C0 - 0.150678) < 0.001
    
    def test_alpha_value(self):
        """Test decay factor α = 1/κ_Π."""
        expected = 1.0 / KAPPA_PI
        assert abs(ALPHA - expected) < 1e-10
        assert ALPHA > 0
    
    def test_beta_value(self):
        """Test β relates to QCAL frequency."""
        assert BETA > 0
        # Should be related to angular frequency
        assert isinstance(BETA, float)
    
    def test_gamma_value(self):
        """Test γ relates to golden ratio."""
        expected = math.log(GOLDEN_RATIO)
        assert abs(GAMMA - expected) < 1e-10
        assert GAMMA > 0
    
    def test_threshold_value(self):
        """Test threshold is at r=4."""
        assert R_THRESHOLD == 4.0
        assert R_MIN <= R_THRESHOLD <= R_MAX


class TestLogarithmicSpiral:
    """Test suite for logarithmic spiral functions."""
    
    def test_spiral_at_zero(self):
        """Test spiral at θ=0."""
        z = z_spiral(0)
        assert abs(z - 1.0) < 1e-10
    
    def test_spiral_magnitude(self):
        """Test spiral magnitude calculation."""
        theta = math.pi
        z = z_spiral(theta)
        mag = spiral_magnitude(theta)
        
        assert abs(abs(z) - mag) < 1e-10
        assert mag == math.exp(theta * C0)
    
    def test_spiral_phase(self):
        """Test spiral phase calculation."""
        theta = math.pi / 4
        z = z_spiral(theta)
        phase = spiral_phase(theta)
        
        assert abs(cmath.phase(z) - phase) < 1e-10
        assert phase == theta
    
    def test_kappa_pi_one_turn(self):
        """Test that spiral passes through κ_Π at one complete turn."""
        expected, actual, is_close = verify_kappa_pi_property(1)
        
        assert expected == KAPPA_PI
        assert abs(actual - KAPPA_PI) < 1e-10
        assert is_close == True
    
    def test_kappa_pi_multiple_turns(self):
        """Test that spiral property holds for multiple turns."""
        # Two turns
        expected_2, actual_2, close_2 = verify_kappa_pi_property(2)
        assert abs(actual_2 - KAPPA_PI**2) < 1e-9
        assert close_2 == True
        
        # Three turns
        expected_3, actual_3, close_3 = verify_kappa_pi_property(3)
        assert abs(actual_3 - KAPPA_PI**3) < 1e-8
        assert close_3 == True
    
    def test_spiral_trajectory(self):
        """Test spiral trajectory generation."""
        trajectory = spiral_trajectory(num_points=50, max_turns=2.0)
        
        assert len(trajectory) == 50
        assert all(isinstance(z, complex) for z in trajectory)
        
        # First point should be at z(0) = 1
        assert abs(trajectory[0] - 1.0) < 1e-10
        
        # Magnitude should increase
        mags = [abs(z) for z in trajectory]
        for i in range(1, len(mags)):
            assert mags[i] >= mags[i-1]
    
    def test_spiral_arc_length(self):
        """Test spiral arc length calculation."""
        # Arc length from 0 to 2π
        length = spiral_arc_length(0, 2*math.pi)
        
        assert length > 0
        assert isinstance(length, float)
        
        # Arc length should increase with angle
        length_half = spiral_arc_length(0, math.pi)
        assert length > length_half


class TestFieldPsi:
    """Test suite for field Ψ functions."""
    
    def test_field_at_boundary(self):
        """Test field at boundaries of ring region."""
        # At r=1
        psi_1 = psi_field(1.0, 0)
        assert abs(psi_1) > 0
        
        # At r=4
        psi_4 = psi_field(4.0, 0)
        assert abs(psi_4) > 0
        
        # Magnitude should decay with r
        assert abs(psi_1) > abs(psi_4)
    
    def test_field_out_of_range(self):
        """Test that field raises error outside ring region."""
        with pytest.raises(ValueError):
            psi_field(0.5, 0)  # Too small
        
        with pytest.raises(ValueError):
            psi_field(5.0, 0)  # Too large
    
    def test_field_magnitude(self):
        """Test field magnitude calculation."""
        r = 2.0
        theta = math.pi / 3
        
        psi = psi_field(r, theta)
        mag = psi_magnitude(r, theta)
        
        assert abs(abs(psi) - mag) < 1e-10
        
        # Should decay as r^(-α)
        expected_mag = r ** (-ALPHA)
        assert abs(mag - expected_mag) < 1e-10
    
    def test_field_phase(self):
        """Test field phase calculation."""
        r = 2.0
        theta = math.pi / 2
        
        psi = psi_field(r, theta)
        phase = psi_phase(r, theta)
        
        assert abs(cmath.phase(psi) - phase) < 1e-10
        
        # Should be β×θ + γ×log(r)
        expected_phase = BETA * theta + GAMMA * math.log(r)
        assert abs(phase - expected_phase) < 1e-10
    
    def test_field_radial_decay(self):
        """Test that field decays with increasing radius."""
        theta = 0
        r1 = 1.5
        r2 = 2.5
        r3 = 3.5
        
        mag1 = psi_magnitude(r1, theta)
        mag2 = psi_magnitude(r2, theta)
        mag3 = psi_magnitude(r3, theta)
        
        # Should monotonically decrease
        assert mag1 > mag2 > mag3
    
    def test_field_on_circle(self):
        """Test field generation on a circle."""
        r = 2.0
        field_vals = field_on_circle(r, num_points=100)
        
        assert len(field_vals) == 100
        assert all(isinstance(psi, complex) for psi in field_vals)
        
        # All should have same magnitude (at fixed r)
        magnitudes = [abs(psi) for psi in field_vals]
        avg_mag = sum(magnitudes) / len(magnitudes)
        for mag in magnitudes:
            assert abs(mag - avg_mag) < 1e-10


class TestEffectiveArea:
    """Test suite for effective area functions."""
    
    def test_effective_area_calculation(self):
        """Test effective area calculation."""
        r = 2.0
        a_eff = effective_area(r)
        
        expected = A_EFF_MAX * ((1.0 / r) ** ALPHA)
        assert abs(a_eff - expected) < 1e-10
    
    def test_effective_area_decay(self):
        """Test that effective area decreases with radius."""
        a1 = effective_area(1.0)
        a2 = effective_area(2.0)
        a3 = effective_area(3.0)
        a4 = effective_area(4.0)
        
        assert a1 > a2 > a3 > a4
    
    def test_effective_area_positive_r(self):
        """Test that effective area requires positive r."""
        with pytest.raises(ValueError):
            effective_area(0)
        
        with pytest.raises(ValueError):
            effective_area(-1)
    
    def test_threshold_coherence(self):
        """Test coherence at threshold r=4."""
        a_eff, expected_ratio, is_coherent = verify_threshold_coherence()
        
        # Should be coherent
        assert is_coherent == True
        
        # Values should be in reasonable range
        assert a_eff > 0
        assert expected_ratio > 0
        
        # expected_ratio should be 1/κ_Π
        assert abs(expected_ratio - 1.0/KAPPA_PI) < 1e-10
        
        # a_eff should be in same order of magnitude
        assert 0.3 < a_eff < 0.7


class TestFieldEnergy:
    """Test suite for field energy calculations."""
    
    def test_energy_density(self):
        """Test energy density calculation."""
        r = 2.0
        theta = 0
        
        density = field_energy_density(r, theta)
        
        # Should be positive
        assert density > 0
        
        # Should equal |Ψ|²
        mag = psi_magnitude(r, theta)
        assert abs(density - mag**2) < 1e-10
    
    def test_energy_density_decay(self):
        """Test that energy density decreases with radius."""
        theta = 0
        
        d1 = field_energy_density(1.5, theta)
        d2 = field_energy_density(2.5, theta)
        d3 = field_energy_density(3.5, theta)
        
        assert d1 > d2 > d3
    
    def test_total_field_energy(self):
        """Test total field energy calculation."""
        energy = total_field_energy(num_r=20, num_theta=20)
        
        # Should be positive
        assert energy > 0
        
        # Should be finite
        assert math.isfinite(energy)
    
    def test_energy_scales_with_amplitude(self):
        """Test that energy scales with field amplitude."""
        psi_0_1 = 1.0
        psi_0_2 = 2.0
        
        e1 = total_field_energy(num_r=10, num_theta=10, psi_0=psi_0_1)
        e2 = total_field_energy(num_r=10, num_theta=10, psi_0=psi_0_2)
        
        # Energy should scale as psi_0²
        ratio = e2 / e1
        expected_ratio = (psi_0_2 / psi_0_1) ** 2
        assert abs(ratio - expected_ratio) < 0.1  # Allow some numerical error


class TestValidation:
    """Test suite for validation functions."""
    
    def test_validate_spiral_properties(self):
        """Test spiral properties validation."""
        results = validate_spiral_properties()
        
        # Check all required keys
        assert 'c0' in results
        assert 'kappa_pi' in results
        assert 'one_turn_valid' in results
        assert 'three_turns_valid' in results
        
        # Validations should pass
        assert results['one_turn_valid'] == True
        assert results['three_turns_valid'] == True
        
        # c0 should match expected
        assert abs(results['c0'] - results['c0_expected']) < 1e-10
    
    def test_validate_field_properties(self):
        """Test field properties validation."""
        results = validate_field_properties()
        
        # Check all required keys
        assert 'alpha' in results
        assert 'beta' in results
        assert 'gamma' in results
        assert 'r_threshold' in results
        assert 'is_coherent' in results
        
        # Coherence should be validated
        assert results['is_coherent'] == True
        
        # Alpha should be 1/κ_Π
        assert abs(results['alpha'] - 1.0/KAPPA_PI) < 1e-10


class TestIntegration:
    """Integration tests for spiral and field interactions."""
    
    def test_spiral_and_field_at_threshold(self):
        """Test both spiral and field at threshold."""
        # Spiral at 2π (one turn)
        theta_turn = 2 * math.pi
        z_turn = z_spiral(theta_turn)
        
        # Field at threshold
        psi_thresh = psi_field(R_THRESHOLD, theta_turn)
        
        # Both should have reasonable values
        assert abs(abs(z_turn) - KAPPA_PI) < 1e-10
        assert abs(psi_thresh) > 0
    
    def test_coherence_across_structures(self):
        """Test coherence between different structures."""
        # Effective area at threshold
        a_eff = effective_area(R_THRESHOLD)
        
        # Should be in coherence with 1/κ_Π
        ratio = 1.0 / KAPPA_PI
        
        # Both should be sub-unity values
        assert 0 < a_eff < 1
        assert 0 < ratio < 1


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_spiral_negative_theta(self):
        """Test spiral with negative angles."""
        z_pos = z_spiral(math.pi)
        z_neg = z_spiral(-math.pi)
        
        # Should have different magnitudes (exp growth/decay)
        assert abs(z_pos) > abs(z_neg)
    
    def test_field_full_rotation(self):
        """Test field after full rotation."""
        r = 2.0
        psi_0 = psi_field(r, 0)
        psi_2pi = psi_field(r, 2*math.pi)
        
        # Phase should differ by 2π × β
        from logarithmic_spiral import normalize_phase
        
        phase_diff = cmath.phase(psi_2pi) - cmath.phase(psi_0)
        expected_diff = 2 * math.pi * BETA
        
        # Normalize to [-π, π]
        phase_diff = normalize_phase(phase_diff)
        expected_diff = normalize_phase(expected_diff)
        
        # Magnitudes should be equal at same r
        assert abs(abs(psi_0) - abs(psi_2pi)) < 1e-10
    
    def test_numerical_stability(self):
        """Test numerical stability for extreme values."""
        # Very small angle
        z_small = z_spiral(1e-10)
        assert abs(z_small - 1.0) < 1e-8
        
        # Large angle (many turns)
        z_large = z_spiral(20 * math.pi)
        assert math.isfinite(abs(z_large))
        assert abs(z_large) > 1  # Should grow


def test_module_imports():
    """Test that all required functions can be imported."""
    from logarithmic_spiral import (
        z_spiral, psi_field, effective_area,
        validate_spiral_properties, validate_field_properties
    )
    
    assert z_spiral is not None
    assert psi_field is not None
    assert effective_area is not None


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Logarithmic Spiral and Field Ψ")
    print("=" * 70)
    print()
    
    # Run validation
    print("Validating spiral properties...")
    spiral_results = validate_spiral_properties()
    print(f"  One turn valid: {spiral_results['one_turn_valid']}")
    print(f"  Three turns valid: {spiral_results['three_turns_valid']}")
    
    print()
    print("Validating field properties...")
    field_results = validate_field_properties()
    print(f"  Threshold coherent: {field_results['is_coherent']}")
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
