"""
Test V13 Thermodynamic Limit Validator
=======================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import os
import json
import numpy as np
from v13_limit_validator import V13LimitValidator, KAPPA_INFINITY_TARGET, SYSTEM_SIZES


def test_v13_validator_initialization():
    """Test V13 validator can be initialized"""
    validator = V13LimitValidator()
    assert validator.f0 > 0
    assert validator.kappa_pi > 0
    print("✓ V13 validator initialization successful")


def test_multi_scale_sweep():
    """Test multi-scale sweep produces expected number of results"""
    validator = V13LimitValidator()
    kappa_values, scaled_values = validator.compute_multi_scale_sweep(SYSTEM_SIZES)
    
    assert len(kappa_values) == len(SYSTEM_SIZES)
    assert len(scaled_values) == len(SYSTEM_SIZES)
    assert all(k > 0 for k in kappa_values), "All kappa values should be positive"
    assert all(s > 0 for s in scaled_values), "All scaled values should be positive"
    
    print(f"✓ Multi-scale sweep produced {len(kappa_values)} results")
    print(f"  κ(128) = {kappa_values[0]:.6f}")
    print(f"  κ(2560) = {kappa_values[-1]:.6f}")


def test_extrapolation_fit():
    """Test κ_∞ extrapolation produces reasonable results"""
    validator = V13LimitValidator()
    kappa_values, scaled_values = validator.compute_multi_scale_sweep(SYSTEM_SIZES)
    fit_results = validator.extrapolate_kappa_infinity(SYSTEM_SIZES, kappa_values, scaled_values)
    
    assert fit_results['fit_success'], "Fit should succeed"
    assert 'kappa_infinity' in fit_results
    assert 'fit_exponent_alpha' in fit_results
    
    kappa_inf = fit_results['kappa_infinity']
    alpha = fit_results['fit_exponent_alpha']
    rel_error = fit_results['relative_error']
    
    # Check results are in reasonable range
    assert 2.0 < kappa_inf < 3.0, f"κ_∞ should be near κ_Π, got {kappa_inf}"
    assert 0.1 < alpha < 1.0, f"Exponent α should be between 0.1 and 1.0, got {alpha}"
    assert rel_error < 0.05, f"Relative error should be < 5%, got {rel_error*100:.2f}%"
    
    print(f"✓ Extrapolation successful:")
    print(f"  κ_∞ = {kappa_inf:.6f}")
    print(f"  α = {alpha:.4f}")
    print(f"  Error = {rel_error*100:.2f}%")


def test_number_variance():
    """Test number variance calculation"""
    validator = V13LimitValidator()
    
    # Generate some test eigenvalues
    eigenvalues = np.sort(np.random.rand(100))
    
    L_values, sigma2_values = validator.compute_number_variance(eigenvalues, L_max=20.0, num_points=20)
    
    assert len(L_values) == 20
    assert len(sigma2_values) == 20
    assert all(sigma2 >= 0 for sigma2 in sigma2_values), "Variance should be non-negative"
    
    print(f"✓ Number variance calculation successful")
    print(f"  Computed for {len(L_values)} intervals")


def test_goe_predictions():
    """Test GOE and Poisson predictions"""
    validator = V13LimitValidator()
    
    L_values = np.array([1, 5, 10, 20, 50])
    
    sigma2_goe = validator.goe_number_variance(L_values)
    sigma2_poisson = validator.poisson_number_variance(L_values)
    
    # GOE should be logarithmic (grow slower than L)
    assert sigma2_goe[-1] < sigma2_poisson[-1], "GOE should show rigidity (less variance than Poisson)"
    
    # Poisson should be linear
    np.testing.assert_array_almost_equal(sigma2_poisson, L_values, decimal=10)
    
    print(f"✓ GOE and Poisson predictions correct")


def test_class_B_verification():
    """Test class 𝔅 property verification"""
    validator = V13LimitValidator()
    
    properties = validator.verify_class_B_properties(N=128)
    
    assert isinstance(properties, dict)
    assert 'P1_Periodicity' in properties
    assert 'P2_Real_Symmetric' in properties
    assert 'P3_Ramsey_Density' in properties
    assert 'P4_Riemann_Alignment' in properties
    
    # P1 and P2 should be verified
    assert properties['P1_Periodicity'], "Periodicity should be verified"
    assert properties['P2_Real_Symmetric'], "Real & Symmetric should be verified"
    
    print(f"✓ Class 𝔅 verification complete")
    print(f"  P1 (Periodicity): {'✓' if properties['P1_Periodicity'] else '✗'}")
    print(f"  P2 (Real & Symmetric): {'✓' if properties['P2_Real_Symmetric'] else '✗'}")


def test_output_files_exist():
    """Test that output files are created"""
    # Check if files exist from previous run
    assert os.path.exists('v13_limit_results.json'), "JSON results file should exist"
    assert os.path.exists('v13_scaling_rigidity.png'), "Plot file should exist"
    
    # Validate JSON structure
    with open('v13_limit_results.json', 'r') as f:
        results = json.load(f)
    
    assert 'kappa_infinity' in results
    assert 'system_sizes' in results
    assert 'scaled_values' in results
    assert 'L_values' in results
    assert 'sigma2_values' in results
    assert 'class_B_properties' in results
    
    print(f"✓ Output files exist and valid")
    print(f"  κ_∞ = {results['kappa_infinity']:.6f}")
    print(f"  Error = {results['relative_error_percent']:.4f}%")


def run_tests():
    """Run all V13 tests"""
    print("="*70)
    print(" V13 THERMODYNAMIC LIMIT VALIDATOR - TEST SUITE ".center(70))
    print("="*70)
    print()
    
    tests = [
        ("Validator Initialization", test_v13_validator_initialization),
        ("Multi-Scale Sweep", test_multi_scale_sweep),
        ("Extrapolation Fit", test_extrapolation_fit),
        ("Number Variance", test_number_variance),
        ("GOE/Poisson Predictions", test_goe_predictions),
        ("Class 𝔅 Verification", test_class_B_verification),
        ("Output Files", test_output_files_exist),
    ]
    
    passed = 0
    failed = 0
    
    for test_name, test_func in tests:
        print(f"\n{test_name}")
        print("-" * 70)
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ ERROR: {e}")
            failed += 1
    
    print()
    print("="*70)
    print(f"RESULTS: {passed} passed, {failed} failed out of {len(tests)} tests")
    print("="*70)
    
    if failed == 0:
        print("\n✓ ALL TESTS PASSED - V13 VALIDATOR OPERATIONAL")
    else:
        print(f"\n✗ {failed} TEST(S) FAILED - REVIEW REQUIRED")
    
    return failed == 0


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
