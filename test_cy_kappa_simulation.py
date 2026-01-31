#!/usr/bin/env python3
"""
Test suite for Calabi-Yau κ_Π distribution simulation
Tests the fundamental calculations and data generation
"""

import numpy as np
import os
import sys

def test_fundamental_constants():
    """Test that fundamental constants are correct."""
    phi = (1 + np.sqrt(5)) / 2
    ln_phi2 = np.log(phi**2)
    
    assert abs(phi - 1.6180339887) < 1e-9, "φ calculation incorrect"
    assert abs(phi**2 - 2.6180339887) < 1e-9, "φ² calculation incorrect"
    assert abs(ln_phi2 - 0.9624236501) < 1e-9, "ln(φ²) calculation incorrect"
    
    print("✓ Fundamental constants test passed")
    return True


def test_kappa_calculations():
    """Test κ_Π calculations for known values."""
    phi = (1 + np.sqrt(5)) / 2
    ln_phi2 = np.log(phi**2)
    
    # Expected values calculated correctly
    test_cases = [
        (10, 2.3925),
        (12, 2.5819),
        (13, 2.6651),
        (21, 3.1634),
        (34, 3.6640),
        (55, 4.1638),
        (89, 4.6639),
    ]
    
    for N, expected in test_cases:
        kappa = np.log(N) / ln_phi2
        assert abs(kappa - expected) < 0.001, f"κ_Π({N}) = {kappa:.4f}, expected {expected:.4f}"
    
    print("✓ κ_Π calculations test passed")
    return True


def test_inverse_calculation():
    """Test inverse calculation: given κ_Π, find N."""
    phi = (1 + np.sqrt(5)) / 2
    ln_phi2 = np.log(phi**2)
    
    target = 2.5773
    N_star = np.exp(target * ln_phi2)
    
    # Verify N_star is near 12
    assert 11.9 < N_star < 12.0, f"N* = {N_star}, expected ~11.95"
    
    # Verify inverse gives us back the target
    kappa_check = np.log(N_star) / ln_phi2
    assert abs(kappa_check - target) < 1e-10, "Inverse calculation doesn't round-trip"
    
    print("✓ Inverse calculation test passed")
    return True


def test_dataset_generation():
    """Test that dataset generation produces valid data."""
    # Import the function from the main script
    sys.path.insert(0, os.path.dirname(__file__))
    
    # Set seed for reproducibility
    np.random.seed(42)
    
    from simulate_cy_kappa_distribution import load_realistic_cy_dataset
    
    N_vals, κ_vals = load_realistic_cy_dataset()
    
    # Check sizes
    assert len(N_vals) == len(κ_vals), "N and κ arrays have different lengths"
    assert len(N_vals) > 900, f"Dataset too small: {len(N_vals)} samples"
    
    # Check ranges
    assert np.all(N_vals >= 10), "Some N values are below 10"
    assert np.all(N_vals <= 500), "Some N values are above 500"
    
    # Check that κ_Π values are correctly computed
    phi = (1 + np.sqrt(5)) / 2
    ln_phi2 = np.log(phi**2)
    
    for i in range(min(100, len(N_vals))):
        expected_kappa = np.log(N_vals[i]) / ln_phi2
        assert abs(κ_vals[i] - expected_kappa) < 1e-10, f"κ_Π mismatch at index {i}"
    
    # Check that we have significant clustering around target
    cluster_count = np.sum((κ_vals > 2.4) & (κ_vals < 2.7))
    cluster_fraction = cluster_count / len(κ_vals)
    assert cluster_fraction > 0.2, f"Insufficient clustering: {cluster_fraction*100:.1f}%"
    
    print(f"✓ Dataset generation test passed ({len(N_vals)} samples, {cluster_fraction*100:.1f}% in cluster zone)")
    return True


def test_fibonacci_sequence():
    """Test that Fibonacci numbers produce increasing κ_Π values."""
    phi = (1 + np.sqrt(5)) / 2
    ln_phi2 = np.log(phi**2)
    
    fibonacci = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
    kappa_values = [np.log(n) / ln_phi2 for n in fibonacci if n >= 2]
    
    # Check strictly increasing
    for i in range(len(kappa_values) - 1):
        assert kappa_values[i] < kappa_values[i+1], "κ_Π not strictly increasing"
    
    print("✓ Fibonacci sequence test passed")
    return True


def run_all_tests():
    """Run all tests."""
    print("=" * 60)
    print("Running Calabi-Yau κ_Π Simulation Tests")
    print("=" * 60)
    print()
    
    tests = [
        ("Fundamental Constants", test_fundamental_constants),
        ("κ_Π Calculations", test_kappa_calculations),
        ("Inverse Calculation", test_inverse_calculation),
        ("Dataset Generation", test_dataset_generation),
        ("Fibonacci Sequence", test_fibonacci_sequence),
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            print(f"Testing {name}...")
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"✗ {name} FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {name} ERROR: {e}")
            failed += 1
        print()
    
    print("=" * 60)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
