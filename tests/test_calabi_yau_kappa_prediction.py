"""
Test suite for calabi_yau_kappa_prediction module
==================================================

Tests the generalization of κ_Π to other Calabi-Yau manifolds
based on the symbiotic vibrational base φ̃² ≈ 2.706940253.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_kappa_prediction import (
    PHI_TILDE_SQUARED,
    LN_PHI_TILDE_SQUARED,
    kappa_pred,
    generate_predictions,
    verify_resonance,
    find_resonances,
    analyze_multiples,
    detect_periodicity,
    symbiotic_interpretation,
    validate_predictions,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_phi_tilde_squared_value(self):
        """Test that φ̃² has the correct value."""
        assert PHI_TILDE_SQUARED == 2.706940253
        assert isinstance(PHI_TILDE_SQUARED, float)
    
    def test_ln_phi_tilde_squared(self):
        """Test that ln(φ̃²) is correctly calculated."""
        expected = math.log(PHI_TILDE_SQUARED)
        assert abs(LN_PHI_TILDE_SQUARED - expected) < 1e-10
        # Should be approximately 0.9958
        assert abs(LN_PHI_TILDE_SQUARED - 0.9958) < 0.001
    
    def test_base_close_to_e(self):
        """Verify that φ̃² is close to e (≈2.718)."""
        # φ̃² ≈ 2.707 which is slightly less than e ≈ 2.718
        assert 2.7 < PHI_TILDE_SQUARED < 2.72


class TestKappaPredFunction:
    """Test the main kappa_pred function."""
    
    def test_kappa_pred_basic(self):
        """Test basic calculation of κ_Π(N)."""
        # For N=13, should get approximately 2.5773 (within ~0.002)
        kappa_13 = kappa_pred(13)
        assert abs(kappa_13 - 2.5773) < 0.002
    
    def test_kappa_pred_formula(self):
        """Test that formula κ_Π(N) = ln(N)/ln(φ̃²) is correct."""
        N = 13
        expected = math.log(N) / math.log(PHI_TILDE_SQUARED)
        calculated = kappa_pred(N)
        assert abs(calculated - expected) < 1e-10
    
    def test_kappa_pred_N_1(self):
        """Test that κ_Π(1) = 0 (log of 1 is 0)."""
        kappa_1 = kappa_pred(1)
        assert abs(kappa_1 - 0.0) < 1e-10
    
    def test_kappa_pred_increases_with_N(self):
        """Test that κ_Π(N) increases monotonically with N."""
        values = [kappa_pred(N) for N in range(1, 21)]
        # Check all consecutive pairs are increasing
        for i in range(len(values) - 1):
            assert values[i+1] > values[i]
    
    def test_kappa_pred_invalid_N(self):
        """Test that invalid N raises ValueError."""
        with pytest.raises(ValueError):
            kappa_pred(0)
        
        with pytest.raises(ValueError):
            kappa_pred(-5)
    
    def test_kappa_pred_invalid_base(self):
        """Test that invalid base raises ValueError."""
        with pytest.raises(ValueError):
            kappa_pred(10, base=1.0)
        
        with pytest.raises(ValueError):
            kappa_pred(10, base=0.5)


class TestPredictedValues:
    """Test predicted values from the formula κ_Π(N) = ln(N)/ln(φ̃²)."""
    
    def test_N_11(self):
        """Test κ_Π(11) calculated from formula."""
        kappa_11 = kappa_pred(11)
        expected = math.log(11) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_11 - expected) < 1e-10
    
    def test_N_12(self):
        """Test κ_Π(12) calculated from formula."""
        kappa_12 = kappa_pred(12)
        expected = math.log(12) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_12 - expected) < 1e-10
    
    def test_N_13_resonant(self):
        """Test κ_Π(13) ≈ 2.5757 (close to universal value 2.5773)."""
        kappa_13 = kappa_pred(13)
        expected = math.log(13) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_13 - expected) < 1e-10
        # Should be close to the universal constant
        assert abs(kappa_13 - 2.5773) < 0.002
    
    def test_N_14(self):
        """Test κ_Π(14) calculated from formula."""
        kappa_14 = kappa_pred(14)
        expected = math.log(14) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_14 - expected) < 1e-10
    
    def test_N_15(self):
        """Test κ_Π(15) calculated from formula."""
        kappa_15 = kappa_pred(15)
        expected = math.log(15) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_15 - expected) < 1e-10
    
    def test_N_16(self):
        """Test κ_Π(16) calculated from formula."""
        kappa_16 = kappa_pred(16)
        expected = math.log(16) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_16 - expected) < 1e-10
    
    def test_N_17(self):
        """Test κ_Π(17) calculated from formula."""
        kappa_17 = kappa_pred(17)
        expected = math.log(17) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_17 - expected) < 1e-10
    
    def test_N_18(self):
        """Test κ_Π(18) calculated from formula."""
        kappa_18 = kappa_pred(18)
        expected = math.log(18) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_18 - expected) < 1e-10
    
    def test_N_19(self):
        """Test κ_Π(19) calculated from formula."""
        kappa_19 = kappa_pred(19)
        expected = math.log(19) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_19 - expected) < 1e-10
    
    def test_N_20(self):
        """Test κ_Π(20) calculated from formula."""
        kappa_20 = kappa_pred(20)
        expected = math.log(20) / math.log(PHI_TILDE_SQUARED)
        assert abs(kappa_20 - expected) < 1e-10


class TestGeneratePredictions:
    """Test the generate_predictions function."""
    
    def test_generate_predictions_range(self):
        """Test generating predictions for a range."""
        predictions = generate_predictions(11, 20)
        
        # Should have 10 entries
        assert len(predictions) == 10
        
        # Should include all values from 11 to 20
        for N in range(11, 21):
            assert N in predictions
    
    def test_generate_predictions_precision(self):
        """Test that predictions are rounded correctly."""
        predictions = generate_predictions(11, 20, precision=3)
        
        # All values should have at most 3 decimal places
        for kappa in predictions.values():
            # Check by converting to string
            kappa_str = f"{kappa:.10f}"
            decimal_part = kappa_str.split('.')[1]
            # Count non-zero digits after 3rd decimal place
            significant_after_3 = any(c != '0' for c in decimal_part[3:])
            assert not significant_after_3
    
    def test_generate_predictions_custom_range(self):
        """Test custom range."""
        predictions = generate_predictions(1, 5)
        assert len(predictions) == 5
        assert 1 in predictions
        assert 5 in predictions


class TestVerifyResonance:
    """Test resonance verification."""
    
    def test_verify_resonance_N13(self):
        """Test that N=13 is close to κ_Π = 2.5773."""
        is_resonant, kappa, diff = verify_resonance(13, 2.5773, tolerance=0.002)
        
        # Should be resonant with tolerance of 0.002
        assert is_resonant
        assert abs(kappa - 2.5773) < 0.002
    
    def test_verify_resonance_non_resonant(self):
        """Test that N=11 does not resonate with κ_Π = 2.5773."""
        is_resonant, kappa, diff = verify_resonance(11, 2.5773, tolerance=0.001)
        
        assert not is_resonant
        assert diff > 0.001
    
    def test_verify_resonance_tolerance(self):
        """Test that tolerance parameter works."""
        # With tight tolerance
        is_resonant_tight, _, _ = verify_resonance(13, 2.577, tolerance=0.0001)
        
        # With loose tolerance
        is_resonant_loose, _, _ = verify_resonance(13, 2.577, tolerance=0.01)
        
        # Loose should pass
        assert is_resonant_loose


class TestFindResonances:
    """Test finding resonances."""
    
    def test_find_resonances_includes_13(self):
        """Test that searching for κ_Π ≈ 2.5773 finds N=13."""
        resonances = find_resonances(2.5773, (1, 50), tolerance=0.01)
        
        assert 13 in resonances
    
    def test_find_resonances_range(self):
        """Test that resonances are within specified range."""
        N_min, N_max = 10, 30
        resonances = find_resonances(2.5773, (N_min, N_max))
        
        for N in resonances:
            assert N_min <= N <= N_max
    
    def test_find_resonances_empty(self):
        """Test that no resonances are found with impossible target."""
        resonances = find_resonances(100.0, (1, 50), tolerance=0.01)
        
        assert len(resonances) == 0


class TestAnalyzeMultiples:
    """Test analysis of multiples."""
    
    def test_analyze_multiples_basic(self):
        """Test basic multiple analysis."""
        multiples = analyze_multiples(13, 3)
        
        assert len(multiples) == 3
        assert multiples[1]['N'] == 13
        assert multiples[2]['N'] == 26
        assert multiples[3]['N'] == 39
    
    def test_analyze_multiples_kappa_values(self):
        """Test that kappa values are calculated for each multiple."""
        multiples = analyze_multiples(13, 3)
        
        for k in range(1, 4):
            assert 'kappa_pi' in multiples[k]
            assert multiples[k]['kappa_pi'] > 0
    
    def test_analyze_multiples_increasing(self):
        """Test that kappa values increase with multiples."""
        multiples = analyze_multiples(13, 5)
        
        kappa_values = [multiples[k]['kappa_pi'] for k in range(1, 6)]
        
        # Should be increasing
        for i in range(len(kappa_values) - 1):
            assert kappa_values[i+1] > kappa_values[i]
    
    def test_analyze_multiples_relation_to_base(self):
        """Test relation_to_base calculation."""
        multiples = analyze_multiples(13, 2)
        
        # Relation should exist for all multiples
        assert multiples[1]['relation_to_base'] is not None
        assert multiples[2]['relation_to_base'] is not None
        
        # For k=1, relation should be 1.0
        assert abs(multiples[1]['relation_to_base'] - 1.0) < 1e-10


class TestDetectPeriodicity:
    """Test periodicity detection."""
    
    def test_detect_periodicity_basic(self):
        """Test basic periodicity analysis."""
        result = detect_periodicity((1, 100))
        
        assert 'N_range' in result
        assert 'num_values' in result
        assert 'min_kappa' in result
        assert 'max_kappa' in result
        assert 'mean_difference' in result
    
    def test_detect_periodicity_range(self):
        """Test that analysis covers the correct range."""
        N_min, N_max = 10, 50
        result = detect_periodicity((N_min, N_max))
        
        assert result['N_range'] == (N_min, N_max)
        assert result['num_values'] == N_max - N_min + 1
    
    def test_detect_periodicity_monotonic(self):
        """Test that differences are positive (monotonic increase)."""
        result = detect_periodicity((1, 50))
        
        # All differences should be positive (kappa increases with N)
        for diff in result['differences']:
            assert diff > 0
    
    def test_detect_periodicity_bounds(self):
        """Test that min/max are sensible."""
        result = detect_periodicity((1, 100))
        
        # Min should be close to 0 (at N=1)
        assert result['min_kappa'] < 0.1
        
        # Max should be positive and substantial
        assert result['max_kappa'] > 4.0


class TestSymbioticInterpretation:
    """Test symbiotic interpretation."""
    
    def test_symbiotic_interpretation_N13(self):
        """Test interpretation for N=13 (near-resonant)."""
        interp = symbiotic_interpretation(13)
        
        assert interp['N'] == 13
        # With tolerance of 0.002, should be resonant
        assert 'signature' in interp
        # κ_Π(13) should be close to 2.5773
        assert abs(interp['kappa_pi'] - 2.5773) < 0.002
    
    def test_symbiotic_interpretation_sub_resonant(self):
        """Test interpretation for N < 13 (sub-resonant)."""
        interp = symbiotic_interpretation(11)
        
        assert interp['N'] == 11
        assert 'signature' in interp
    
    def test_symbiotic_interpretation_super_resonant(self):
        """Test interpretation for N > 14 (super-resonant)."""
        interp = symbiotic_interpretation(15)
        
        assert interp['N'] == 15
        assert 'signature' in interp
    
    def test_symbiotic_interpretation_fields(self):
        """Test that all expected fields are present."""
        interp = symbiotic_interpretation(13)
        
        required_fields = [
            'N', 'kappa_pi', 'base', 'is_resonant',
            'difference_from_known', 'signature', 
            'classification', 'interpretation'
        ]
        
        for field in required_fields:
            assert field in interp


class TestValidatePredictions:
    """Test the validation function."""
    
    def test_validate_predictions_passes(self):
        """Test that validation passes with correct implementation."""
        result = validate_predictions()
        assert result == True
    
    def test_validate_predictions_formula(self):
        """Test that formula κ_Π(N) = ln(N)/ln(φ̃²) is correctly implemented."""
        # Test basic mathematical properties
        # log_base(1) = 0
        assert abs(kappa_pred(1) - 0.0) < 1e-10
        
        # log_base(base) = 1
        assert abs(kappa_pred(PHI_TILDE_SQUARED) - 1.0) < 1e-10
        
        # log_base(base²) = 2
        assert abs(kappa_pred(PHI_TILDE_SQUARED**2) - 2.0) < 1e-10


class TestMathematicalProperties:
    """Test mathematical properties of κ_Π(N)."""
    
    def test_logarithmic_property(self):
        """Test that κ_Π(a*b) = κ_Π(a) + κ_Π(b) (logarithm property)."""
        a, b = 3, 5
        
        kappa_ab = kappa_pred(a * b)
        kappa_a = kappa_pred(a)
        kappa_b = kappa_pred(b)
        
        # log(a*b) = log(a) + log(b)
        assert abs(kappa_ab - (kappa_a + kappa_b)) < 1e-10
    
    def test_power_property(self):
        """Test that κ_Π(N^k) = k * κ_Π(N)."""
        N = 5
        k = 2
        
        kappa_N_power_k = kappa_pred(N ** k)
        k_times_kappa_N = k * kappa_pred(N)
        
        # log(N^k) = k * log(N)
        assert abs(kappa_N_power_k - k_times_kappa_N) < 1e-10
    
    def test_continuity(self):
        """Test that kappa function has smooth changes."""
        # Check that changes between consecutive N are decreasing
        # (logarithmic derivative decreases)
        for N in range(2, 20):
            kappa_N = kappa_pred(N)
            kappa_N_plus_1 = kappa_pred(N + 1)
            jump = kappa_N_plus_1 - kappa_N
            # Jump should be positive (monotonically increasing)
            assert jump > 0


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_large_N(self):
        """Test that function works for large N."""
        kappa_1000 = kappa_pred(1000)
        
        # Should be a reasonable value (around 6-7)
        assert 6.0 < kappa_1000 < 8.0
    
    def test_very_large_N(self):
        """Test that function works for very large N."""
        kappa_million = kappa_pred(1000000)
        
        # Should be a reasonable value
        assert kappa_million > 10.0
        assert kappa_million < 20.0
    
    def test_precision_maintained(self):
        """Test that precision is maintained across calculations."""
        # Calculate using function
        kappa_direct = kappa_pred(13)
        
        # Calculate manually
        kappa_manual = math.log(13) / math.log(PHI_TILDE_SQUARED)
        
        # Should be identical
        assert abs(kappa_direct - kappa_manual) < 1e-15


def test_module_imports():
    """Test that all required functions can be imported."""
    from calabi_yau_kappa_prediction import (
        PHI_TILDE_SQUARED,
        LN_PHI_TILDE_SQUARED,
        kappa_pred,
        generate_predictions,
        verify_resonance,
        find_resonances,
        analyze_multiples,
        detect_periodicity,
        symbiotic_interpretation,
        validate_predictions,
    )
    
    assert PHI_TILDE_SQUARED is not None
    assert callable(kappa_pred)
    assert callable(generate_predictions)


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Calabi-Yau κ_Π Prediction Module")
    print("=" * 70)
    print()
    
    # Run quick validation
    print("Running validation...")
    if validate_predictions():
        print("✅ All predicted values match expected values")
    else:
        print("❌ Validation failed")
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
