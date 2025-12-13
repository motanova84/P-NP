#!/usr/bin/env python3
"""
Quick test script to verify kappa_verification.py works correctly.

This test confirms that:
1. All functions can be imported
2. The core functionality produces expected negative kappa values
3. The results are consistent with the problem statement findings
"""

import sys
import numpy as np


def test_imports():
    """Test that all functions can be imported."""
    print("Testing imports...")
    try:
        from kappa_verification import (
            construct_tseitin_incidence,
            compute_spectral_constant,
            verify_kappa_decay,
            plot_results
        )
        print("✓ All imports successful")
        return True
    except ImportError as e:
        print(f"✗ Import failed: {e}")
        return False


def test_core_functionality():
    """Test that the core functions work and produce negative kappa."""
    print("\nTesting core functionality...")
    try:
        from kappa_verification import construct_tseitin_incidence, compute_spectral_constant
        
        # Test with small n
        n = 101
        I, base_G = construct_tseitin_incidence(n, d=8)
        kappa = compute_spectral_constant(I)
        
        # Verify graph structure
        assert I.number_of_nodes() == n + (n * 8 // 2), "Incorrect number of nodes"
        
        # Verify kappa is negative (key finding)
        assert kappa < 0, f"Expected negative kappa, got {kappa}"
        assert -3.0 < kappa < -2.5, f"Kappa {kappa} outside expected range [-3.0, -2.5]"
        
        print(f"✓ Core functionality works (n={n}, kappa={kappa:.4f})")
        return True
        
    except Exception as e:
        print(f"✗ Core functionality test failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def test_consistency():
    """Test that results are consistent across multiple runs."""
    print("\nTesting consistency...")
    try:
        from kappa_verification import construct_tseitin_incidence, compute_spectral_constant
        
        kappas = []
        for _ in range(3):
            I, _ = construct_tseitin_incidence(101, d=8)
            kappa = compute_spectral_constant(I)
            kappas.append(kappa)
        
        # All should be negative
        assert all(k < 0 for k in kappas), "Some kappa values are not negative"
        
        # Should be in similar range (allowing for randomness in graph generation)
        kappa_std = np.std(kappas)
        assert kappa_std < 0.5, f"Too much variation in kappa: std={kappa_std}"
        
        print(f"✓ Results are consistent (kappas: {[f'{k:.4f}' for k in kappas]})")
        return True
        
    except Exception as e:
        print(f"✗ Consistency test failed: {e}")
        return False


def main():
    """Run all tests."""
    print("="*70)
    print("Kappa Verification Module Test Suite")
    print("="*70)
    
    tests = [
        test_imports,
        test_core_functionality,
        test_consistency,
    ]
    
    results = []
    for test in tests:
        results.append(test())
    
    print("\n" + "="*70)
    print(f"Test Results: {sum(results)}/{len(results)} passed")
    print("="*70)
    
    if all(results):
        print("\n✅ All tests passed!")
        return 0
    else:
        print("\n❌ Some tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
