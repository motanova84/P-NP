#!/usr/bin/env python3
"""
Test script for holographic_verification.py

Validates the holographic verification calculations and output.
"""

import sys
import os

# Add parent directory to path to import holographic_verification
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from holographic_verification import HolographicVerification, KAPPA_PI, ALPHA_ADS3
import math


def test_effective_mass():
    """Test effective mass calculation."""
    verifier = HolographicVerification()
    
    # Test n=10
    meff_10 = verifier.compute_effective_mass(10)
    assert meff_10 > 10, "Effective mass should be greater than base value"
    assert meff_10 < 12, "Effective mass should be reasonable"
    
    # Test n=100
    meff_100 = verifier.compute_effective_mass(100)
    assert meff_100 > meff_10, "Effective mass should increase with n"
    
    print("✅ test_effective_mass passed")


def test_ryu_takayanagi_volume():
    """Test Ryu-Takayanagi volume calculation."""
    verifier = HolographicVerification()
    
    # Test basic properties
    meff_10 = verifier.compute_effective_mass(10)
    vol_10 = verifier.compute_ryu_takayanagi_volume(10, meff_10)
    
    meff_20 = verifier.compute_effective_mass(20)
    vol_20 = verifier.compute_ryu_takayanagi_volume(20, meff_20)
    
    assert vol_10 > 0, "Volume should be positive"
    assert vol_20 > vol_10, "Volume should increase with n"
    
    # Verify Ω(n log n) scaling
    ratio = vol_20 / vol_10
    expected_ratio = (20 * math.log(21)) / (10 * math.log(11))
    assert abs(ratio - expected_ratio) / expected_ratio < 0.5, "Should scale as n log n"
    
    print("✅ test_ryu_takayanagi_volume passed")


def test_holographic_time_bound():
    """Test holographic time bound calculation."""
    verifier = HolographicVerification()
    
    vol_50 = 50.0
    t_holo = verifier.compute_holographic_time_bound(vol_50)
    
    # Should be exponential in volume
    expected = math.exp(ALPHA_ADS3 * vol_50)
    assert abs(t_holo - expected) < 1e-6, "Should compute exp(alpha * vol)"
    
    # Test monotonicity
    t_holo_100 = verifier.compute_holographic_time_bound(100.0)
    assert t_holo_100 > t_holo, "Time should increase with volume"
    
    print("✅ test_holographic_time_bound passed")


def test_cdcl_time():
    """Test CDCL time estimation."""
    verifier = HolographicVerification()
    
    t_10 = verifier.compute_cdcl_time(10)
    t_20 = verifier.compute_cdcl_time(20)
    
    assert t_10 > 0, "CDCL time should be positive"
    assert t_20 > t_10, "CDCL time should increase with n"
    
    # Verify exponential growth
    assert t_20 / t_10 > 1.2, "Should grow exponentially"
    
    print("✅ test_cdcl_time passed")


def test_polynomial_time():
    """Test polynomial time calculation."""
    verifier = HolographicVerification()
    
    t_10 = verifier.compute_polynomial_time(10, degree=3)
    t_20 = verifier.compute_polynomial_time(20, degree=3)
    
    assert t_10 == 1000, "Should compute n^3 correctly"
    assert t_20 == 8000, "Should compute n^3 correctly"
    
    print("✅ test_polynomial_time passed")


def test_separation_verification():
    """Test the full separation verification."""
    verifier = HolographicVerification()
    
    # Use larger n values to see the separation
    n_values = [50, 100]
    results = verifier.verify_separation(n_values)
    
    # Check all required fields are present
    required_fields = ['n', 'meff', 'vol_rt', 't_cdcl', 't_holo', 't_poly', 
                      'separation_cdcl', 'separation_poly']
    for field in required_fields:
        assert field in results, f"Results should contain {field}"
        assert len(results[field]) == len(n_values), f"Should have values for all n"
    
    # Verify T_Holo > T_poly for large n (the key separation)
    # For n=100, we should see clear separation
    assert results['t_holo'][-1] > results['t_poly'][-1], \
        "Holographic bound should exceed polynomial time for n=100"
    
    # Verify monotonicity: T_Holo should grow faster than T_poly
    ratio_50 = results['t_holo'][0] / results['t_poly'][0]
    ratio_100 = results['t_holo'][1] / results['t_poly'][1]
    assert ratio_100 > ratio_50, "Separation should increase with n"
    
    print("✅ test_separation_verification passed")


def test_constants():
    """Test that constants are correctly defined."""
    assert KAPPA_PI == 2.5773, "KAPPA_PI should be 2.5773"
    assert abs(ALPHA_ADS3 - 1/(8*math.pi)) < 1e-6, "ALPHA_ADS3 should be 1/(8π)"
    
    print("✅ test_constants passed")


def main():
    """Run all tests."""
    print("\n" + "="*80)
    print("Testing holographic_verification.py")
    print("="*80 + "\n")
    
    try:
        test_constants()
        test_effective_mass()
        test_ryu_takayanagi_volume()
        test_holographic_time_bound()
        test_cdcl_time()
        test_polynomial_time()
        test_separation_verification()
        
        print("\n" + "="*80)
        print("✅ ALL TESTS PASSED")
        print("="*80 + "\n")
        return 0
        
    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}\n")
        return 1
    except Exception as e:
        print(f"\n❌ UNEXPECTED ERROR: {e}\n")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
