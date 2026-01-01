#!/usr/bin/env python3
"""
test_teorema_infinity_cubed.py - Tests for Teorema ∞³ (κ_Π–φ²–13)

Test suite for the Teorema Infinity Cubed implementation.

© JMMB | P vs NP Verification System
"""

import sys
import os
import math
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from teorema_infinity_cubed import (
    TeoremaInfinityCubed,
    PHI,
    PHI_SQUARED,
    N_SPECIAL,
    KAPPA_PI_13,
    LN_PHI_SQUARED,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_phi_value(self):
        """Test golden ratio value."""
        assert abs(PHI - 1.618033988749895) < 1e-10
        assert abs(PHI - (1 + math.sqrt(5))/2) < 1e-15
    
    def test_phi_squared_value(self):
        """Test φ² value."""
        assert abs(PHI_SQUARED - 2.618033988749895) < 1e-10
        assert abs(PHI_SQUARED - PHI**2) < 1e-15
    
    def test_phi_squared_property(self):
        """Test that φ² = φ + 1."""
        assert abs(PHI_SQUARED - (PHI + 1)) < 1e-15
    
    def test_ln_phi_squared(self):
        """Test ln(φ²) value."""
        expected = math.log(PHI_SQUARED)
        assert abs(LN_PHI_SQUARED - expected) < 1e-15
    
    def test_N_special(self):
        """Test special N value."""
        assert N_SPECIAL == 13
    
    def test_kappa_13(self):
        """Test κ_Π(13) value."""
        expected = math.log(13) / math.log(PHI_SQUARED)
        assert abs(KAPPA_PI_13 - expected) < 1e-10
        # Should be approximately 2.6651
        assert abs(KAPPA_PI_13 - 2.6651) < 0.001


class TestKappaPiCalculation:
    """Test κ_Π calculation functions."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_kappa_pi_basic(self):
        """Test basic κ_Π calculation."""
        # For N = 13
        kappa = self.theorem.kappa_pi(13)
        assert abs(kappa - KAPPA_PI_13) < 1e-10
    
    def test_kappa_pi_various_values(self):
        """Test κ_Π for various N values."""
        test_cases = [
            (1, 0.0),  # log(1) = 0, so κ_Π(1) = 0
            (10, math.log(10) / LN_PHI_SQUARED),
            (12, math.log(12) / LN_PHI_SQUARED),
            (13, KAPPA_PI_13),
            (14, math.log(14) / LN_PHI_SQUARED),
            (100, math.log(100) / LN_PHI_SQUARED),
        ]
        
        for N, expected in test_cases:
            kappa = self.theorem.kappa_pi(N)
            assert abs(kappa - expected) < 1e-10
            
            # Special case: verify κ_Π(1) = 0 explicitly
            if N == 1:
                assert abs(kappa) < 1e-15, "κ_Π(1) should be exactly 0"
    
    def test_kappa_pi_phi_squared(self):
        """Test that κ_Π(φ²) = 1."""
        kappa = self.theorem.kappa_pi(PHI_SQUARED)
        assert abs(kappa - 1.0) < 1e-10
    
    def test_kappa_pi_monotonic(self):
        """Test that κ_Π is strictly increasing."""
        values = [self.theorem.kappa_pi(N) for N in range(1, 50)]
        
        for i in range(len(values) - 1):
            assert values[i] < values[i+1]
    
    def test_kappa_pi_invalid_input(self):
        """Test κ_Π with invalid input."""
        with pytest.raises(ValueError):
            self.theorem.kappa_pi(0)
        
        with pytest.raises(ValueError):
            self.theorem.kappa_pi(-5)


class TestInverseKappaPi:
    """Test inverse κ_Π calculation."""
    
    # Test constants for millennium constant
    MILLENNIUM_CONSTANT = 2.5773
    N_FOR_MILLENNIUM = 11.947  # Expected N for κ = 2.5773
    TOLERANCE = 0.01  # Tolerance for floating point comparison
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_inverse_kappa_pi_basic(self):
        """Test basic inverse calculation."""
        # For κ = 2.6651, should get N ≈ 13
        N = self.theorem.inverse_kappa_pi(KAPPA_PI_13)
        assert abs(N - 13) < 1e-10
    
    def test_inverse_kappa_pi_roundtrip(self):
        """Test roundtrip: N -> κ -> N."""
        test_values = [5, 10, 13, 20, 50]
        
        for N_original in test_values:
            kappa = self.theorem.kappa_pi(N_original)
            N_recovered = self.theorem.inverse_kappa_pi(kappa)
            assert abs(N_original - N_recovered) < 1e-10
    
    def test_inverse_kappa_pi_millennium_constant(self):
        """Test inverse for millennium constant."""
        # For κ = 2.5773, should get N ≈ 11.947
        N = self.theorem.inverse_kappa_pi(self.MILLENNIUM_CONSTANT)
        assert abs(N - self.N_FOR_MILLENNIUM) < self.TOLERANCE


class TestUniquenessValidation:
    """Test uniqueness validation."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_validate_uniqueness(self):
        """Test uniqueness validation function."""
        result = self.theorem.validate_uniqueness_below_100()
        
        assert 'N_special' in result
        assert result['N_special'] == 13
        assert 'is_unique' in result
        assert result['is_unique'] == True
        assert 'explanation' in result
        assert len(result['explanation']) > 0
    
    def test_millennium_constant_reference(self):
        """Test millennium constant reference in validation."""
        result = self.theorem.validate_uniqueness_below_100()
        
        assert 'millennium_constant' in result
        assert result['millennium_constant'] == 2.5773


class TestClosestValues:
    """Test finding closest values."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_find_closest_integers(self):
        """Test finding closest integers to target."""
        result = self.theorem.find_closest_integers_to_target(2.5773, 30)
        
        # Should return a list
        assert isinstance(result, list)
        assert len(result) > 0
        
        # First element should be closest
        assert result[0]['distance'] <= result[1]['distance']
        
        # N=13 should be marked
        n13_found = False
        for item in result:
            if item['N'] == 13:
                n13_found = True
                assert item['is_N13'] == True
            else:
                assert item['is_N13'] == False
        
        assert n13_found


class TestGeometricInterpretation:
    """Test geometric interpretation."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_geometric_interpretation_structure(self):
        """Test geometric interpretation returns proper structure."""
        result = self.theorem.geometric_interpretation()
        
        # Check required keys
        required_keys = [
            'kappa_pi_definition',
            'phi_squared_significance',
            'hodge_numbers',
            'N_13_interpretation',
            'harmonic_resonance',
        ]
        
        for key in required_keys:
            assert key in result
    
    def test_N13_interpretation(self):
        """Test N=13 specific interpretation."""
        result = self.theorem.geometric_interpretation()
        n13 = result['N_13_interpretation']
        
        assert n13['value'] == 13
        assert 'kappa' in n13
        assert abs(n13['kappa'] - KAPPA_PI_13) < 1e-6


class TestMinimalComplexityConjecture:
    """Test minimal complexity conjecture."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_conjecture_structure(self):
        """Test conjecture returns proper structure."""
        result = self.theorem.minimal_complexity_conjecture()
        
        required_keys = [
            'title',
            'statement',
            'mathematical_form',
            'implications',
            'validation_needed',
        ]
        
        for key in required_keys:
            assert key in result
    
    def test_conjecture_validation_questions(self):
        """Test that validation questions are present."""
        result = self.theorem.minimal_complexity_conjecture()
        
        assert isinstance(result['validation_needed'], list)
        assert len(result['validation_needed']) > 0


class TestDynamicalInterpretation:
    """Test dynamical interpretation."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_dynamical_interpretation_structure(self):
        """Test dynamical interpretation structure."""
        result = self.theorem.dynamical_interpretation()
        
        required_keys = [
            'phi_squared_role',
            'kappa_pi_role',
            'N_role',
            'resonance_condition',
        ]
        
        for key in required_keys:
            assert key in result


class TestVisualization:
    """Test visualization generation."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_plot_generation(self):
        """Test that plot can be generated."""
        import tempfile
        
        with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as tmp:
            plot_path = self.theorem.plot_kappa_curve(save_path=tmp.name)
            
            assert plot_path == tmp.name
            assert os.path.exists(plot_path)
            
            # Clean up
            os.unlink(plot_path)


class TestCompleteAnalysis:
    """Test complete analysis."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_complete_analysis_structure(self):
        """Test complete analysis returns all components."""
        result = self.theorem.complete_analysis()
        
        required_keys = [
            'theorem',
            'uniqueness_validation',
            'geometric_interpretation',
            'minimal_complexity_conjecture',
            'dynamical_interpretation',
        ]
        
        for key in required_keys:
            assert key in result
    
    def test_theorem_component(self):
        """Test theorem component of analysis."""
        result = self.theorem.complete_analysis()
        theorem = result['theorem']
        
        assert theorem['special_value_N'] == 13
        assert 'kappa_at_N13' in theorem
        assert abs(theorem['kappa_at_N13'] - KAPPA_PI_13) < 1e-6


class TestMathematicalProperties:
    """Test mathematical properties."""
    
    def setup_method(self):
        """Set up test instance."""
        self.theorem = TeoremaInfinityCubed()
    
    def test_property_kappa_of_phi_squared_power(self):
        """Test that κ_Π((φ²)^k) = k."""
        for k in [1, 2, 3, 4, 5]:
            N = PHI_SQUARED ** k
            kappa = self.theorem.kappa_pi(N)
            assert abs(kappa - k) < 1e-10
    
    def test_property_N_equals_phi_squared_to_kappa(self):
        """Test that N = (φ²)^κ_Π(N)."""
        test_values = [5, 10, 13, 20, 50]
        
        for N in test_values:
            kappa = self.theorem.kappa_pi(N)
            N_reconstructed = PHI_SQUARED ** kappa
            assert abs(N - N_reconstructed) < 1e-10
    
    def test_logarithmic_base_conversion(self):
        """Test that κ_Π(N) = log_φ²(N)."""
        test_values = [5, 10, 13, 20]
        
        for N in test_values:
            kappa_direct = self.theorem.kappa_pi(N)
            # log_b(x) = ln(x) / ln(b)
            kappa_from_log = math.log(N) / math.log(PHI_SQUARED)
            assert abs(kappa_direct - kappa_from_log) < 1e-15


# ============================================================================
# RUN TESTS
# ============================================================================

if __name__ == "__main__":
    # Run pytest
    pytest.main([__file__, "-v", "--tb=short"])
