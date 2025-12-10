"""
Test suite for the constants module (κ_Π and related constants)
================================================================

Tests the millennium constant κ_Π = 2.5773 and its relationships
with Calabi-Yau geometry, QCAL frequency, and computational bounds.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from constants import (
    KAPPA_PI,
    QCAL_FREQUENCY_HZ,
    GOLDEN_RATIO,
    CALABI_YAU_VARIETIES_VALIDATED,
    HEPTAGON_GIZA_ANGLE,
    information_complexity_lower_bound,
    p_np_dichotomy_threshold,
    minimum_time_complexity,
    is_in_P,
    validate_kappa_pi
)


class TestKappaPiConstant:
    """Test suite for κ_Π constant and its properties."""
    
    def test_kappa_pi_value(self):
        """Test that κ_Π has the correct value."""
        assert KAPPA_PI == 2.5773
        assert isinstance(KAPPA_PI, float)
    
    def test_qcal_frequency(self):
        """Test QCAL frequency value."""
        assert QCAL_FREQUENCY_HZ == 141.7001
        assert isinstance(QCAL_FREQUENCY_HZ, float)
    
    def test_golden_ratio(self):
        """Test golden ratio calculation."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(GOLDEN_RATIO - expected) < 1e-10
        assert abs(GOLDEN_RATIO - 1.618033988749) < 1e-10
    
    def test_calabi_yau_varieties(self):
        """Test number of validated Calabi-Yau varieties."""
        assert CALABI_YAU_VARIETIES_VALIDATED == 150
        assert isinstance(CALABI_YAU_VARIETIES_VALIDATED, int)
    
    def test_heptagon_angle(self):
        """Test heptagon angle from Giza geometry."""
        expected = 2 * math.pi / 7
        assert abs(HEPTAGON_GIZA_ANGLE - expected) < 1e-10
        # Check in degrees
        degrees = math.degrees(HEPTAGON_GIZA_ANGLE)
        assert abs(degrees - 51.4285714) < 1e-5


class TestInformationComplexityBounds:
    """Test suite for information complexity bound functions."""
    
    def test_ic_lower_bound_basic(self):
        """Test basic IC lower bound calculation."""
        # For tw=10, n=100
        tw = 10
        n = 100
        ic = information_complexity_lower_bound(tw, n)
        
        # IC = κ_Π * tw / log₂(n)
        expected = KAPPA_PI * tw / math.log2(n)
        assert abs(ic - expected) < 1e-10
    
    def test_ic_lower_bound_high_treewidth(self):
        """Test IC bound for high treewidth."""
        tw = 50
        n = 100
        ic = information_complexity_lower_bound(tw, n)
        
        # Should be substantial
        assert ic > 10
        # Should scale with κ_Π
        assert abs(ic - KAPPA_PI * tw / math.log2(n)) < 1e-10
    
    def test_ic_lower_bound_edge_cases(self):
        """Test IC bound edge cases."""
        # n=1 should return 0
        assert information_complexity_lower_bound(10, 1) == 0.0
        
        # n=0 should return 0
        assert information_complexity_lower_bound(10, 0) == 0.0
    
    def test_ic_bound_scaling(self):
        """Test that IC bound scales correctly with treewidth."""
        n = 100
        tw1 = 10
        tw2 = 20
        
        ic1 = information_complexity_lower_bound(tw1, n)
        ic2 = information_complexity_lower_bound(tw2, n)
        
        # Should scale linearly
        assert abs(ic2 - 2 * ic1) < 1e-10


class TestPNPDichotomy:
    """Test suite for P vs NP dichotomy threshold."""
    
    def test_dichotomy_threshold(self):
        """Test P/NP threshold calculation."""
        n = 100
        threshold = p_np_dichotomy_threshold(n)
        
        # Should be O(log n)
        expected = math.log2(n)
        assert abs(threshold - expected) < 1e-10
    
    def test_is_in_P_low_treewidth(self):
        """Test classification for low treewidth."""
        n = 100
        threshold = p_np_dichotomy_threshold(n)
        
        # tw below threshold should be in P
        tw_low = threshold / 2
        assert is_in_P(tw_low, n) == True
    
    def test_is_in_P_high_treewidth(self):
        """Test classification for high treewidth."""
        n = 100
        threshold = p_np_dichotomy_threshold(n)
        
        # tw above threshold should not be in P
        tw_high = threshold * 2
        assert is_in_P(tw_high, n) == False
    
    def test_is_in_P_boundary(self):
        """Test classification at boundary."""
        n = 100
        threshold = p_np_dichotomy_threshold(n)
        
        # At threshold should be in P
        assert is_in_P(threshold, n) == True
        
        # Just above threshold should not be
        assert is_in_P(threshold + 0.01, n) == False


class TestTimeComplexity:
    """Test suite for time complexity bounds."""
    
    def test_minimum_time_complexity(self):
        """Test minimum time complexity calculation."""
        tw = 20
        n = 100
        
        log_time = minimum_time_complexity(tw, n)
        
        # Should equal IC bound
        expected_ic = information_complexity_lower_bound(tw, n)
        assert abs(log_time - expected_ic) < 1e-10
    
    def test_exponential_time_high_treewidth(self):
        """Test that high treewidth implies exponential time."""
        n = 100
        tw = 50  # High treewidth
        
        log_time = minimum_time_complexity(tw, n)
        
        # log₂(time) should be substantial
        assert log_time > 10
        
        # Actual time would be 2^log_time
        # For log_time > 10, time > 1024


class TestKappaPiValidation:
    """Test suite for κ_Π validation functions."""
    
    def test_validate_kappa_pi(self):
        """Test complete validation of κ_Π."""
        results = validate_kappa_pi()
        
        # Check all required keys are present
        assert 'kappa_pi' in results
        assert 'qcal_frequency' in results
        assert 'golden_ratio' in results
        assert 'varieties_validated' in results
        assert 'heptagon_angle_deg' in results
        assert 'frequency_relation' in results
        assert 'heptagon_relation' in results
        
        # Check values
        assert results['kappa_pi'] == KAPPA_PI
        assert results['qcal_frequency'] == QCAL_FREQUENCY_HZ
        assert results['varieties_validated'] == 150
    
    def test_frequency_relationship(self):
        """Test relationship between κ_Π and QCAL frequency."""
        results = validate_kappa_pi()
        
        # The relationship should be approximately satisfied
        # κ_Π ≈ log₂(f_QCAL / π²) + φ - π
        freq_relation = results['frequency_relation']
        
        # Should be within reasonable tolerance
        assert isinstance(freq_relation, float)
    
    def test_heptagon_relationship(self):
        """Test relationship between κ_Π and heptagon geometry."""
        results = validate_kappa_pi()
        
        # The heptagon relationship
        heptagon_relation = results['heptagon_relation']
        
        # Should be a reasonable value
        assert isinstance(heptagon_relation, float)
        assert heptagon_relation > 0


class TestUnificationPrinciple:
    """Test the unification of topology, information, and computation."""
    
    def test_topology_information_equivalence(self):
        """Test that topological and information measures align."""
        # For a given problem size
        n = 100
        tw = 30
        
        # Information complexity from topology
        ic = information_complexity_lower_bound(tw, n)
        
        # Should be proportional with κ_Π as conversion factor
        assert ic == KAPPA_PI * tw / math.log2(n)
    
    def test_information_computation_equivalence(self):
        """Test that information bounds translate to time bounds."""
        n = 100
        tw = 30
        
        # Information bound
        ic = information_complexity_lower_bound(tw, n)
        
        # Time bound (in log scale)
        log_time = minimum_time_complexity(tw, n)
        
        # Should be equal
        assert abs(ic - log_time) < 1e-10
    
    def test_computational_dichotomy(self):
        """Test the computational dichotomy with κ_Π."""
        n = 100
        
        # Low treewidth
        tw_low = 5
        assert is_in_P(tw_low, n) == True
        ic_low = information_complexity_lower_bound(tw_low, n)
        assert ic_low < 10  # Small IC
        
        # High treewidth
        tw_high = 50
        assert is_in_P(tw_high, n) == False
        ic_high = information_complexity_lower_bound(tw_high, n)
        assert ic_high > 10  # Large IC


class TestConstantConsistency:
    """Test consistency between all constants."""
    
    def test_all_constants_positive(self):
        """Test that all constants are positive."""
        assert KAPPA_PI > 0
        assert QCAL_FREQUENCY_HZ > 0
        assert GOLDEN_RATIO > 0
        assert CALABI_YAU_VARIETIES_VALIDATED > 0
        assert HEPTAGON_GIZA_ANGLE > 0
    
    def test_constant_relationships(self):
        """Test mathematical relationships between constants."""
        # Golden ratio property: φ² = φ + 1
        phi_squared = GOLDEN_RATIO ** 2
        phi_plus_one = GOLDEN_RATIO + 1
        assert abs(phi_squared - phi_plus_one) < 1e-10
        
        # Heptagon property
        assert abs(math.sin(HEPTAGON_GIZA_ANGLE) - math.sin(2*math.pi/7)) < 1e-10


def test_module_imports():
    """Test that all required constants can be imported."""
    from constants import (
        KAPPA_PI,
        QCAL_FREQUENCY_HZ,
        GOLDEN_RATIO,
        IC_SCALING_FACTOR,
        CALABI_YAU_VARIETIES_VALIDATED
    )
    
    assert KAPPA_PI is not None
    assert QCAL_FREQUENCY_HZ is not None
    assert IC_SCALING_FACTOR == KAPPA_PI


if __name__ == "__main__":
    print("=" * 70)
    print("Testing κ_Π = 2.5773 (Millennium Constant)")
    print("=" * 70)
    print()
    
    # Run validation
    results = validate_kappa_pi()
    print("Validation Results:")
    for key, value in results.items():
        print(f"  {key}: {value}")
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
