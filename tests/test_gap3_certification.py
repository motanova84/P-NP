"""
Test suite for Gap 3 certification module.

This tests the Python implementation of the Gap 3 closure.
"""

import sys
import os

# Add the core directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'core'))

from gap3_certification import (
    GAP_3_CERTIFICATE,
    verify_gap3_closure,
    get_kappa_pi,
    btc_to_cs_conversion,
    print_certification
)


def test_kappa_pi_constant():
    """Test that κ_Π constant is correctly defined."""
    kappa = get_kappa_pi()
    assert kappa == 2.5773, f"Expected κ_Π = 2.5773, got {kappa}"
    print("✓ κ_Π constant test passed")


def test_certificate_structure():
    """Test that the certificate has all required fields."""
    required_fields = [
        "theorem", "status", "method", "dependencies",
        "constants", "result", "witness", "date", "signature"
    ]
    
    for field in required_fields:
        assert field in GAP_3_CERTIFICATE, f"Missing field: {field}"
    
    print("✓ Certificate structure test passed")


def test_constants():
    """Test that all constants are correctly defined."""
    constants = GAP_3_CERTIFICATE["constants"]
    
    assert constants["KAPPA_PI"] == 2.5773
    assert constants["FREQ_QCAL"] == 141.7001
    assert constants["FREQ_LOVE"] == 151.7001
    assert constants["FREQ_MANIFEST"] == 888.0
    
    print("✓ Constants test passed")


def test_conversion_formula():
    """Test BTC to ℂₛ conversion."""
    # Test perfect coherence (ψ = 1.0)
    btc = 1.0
    cs = btc_to_cs_conversion(btc, psi=1.0)
    expected = 1.0 * 2.5773 * 1.0
    assert abs(cs - expected) < 1e-6, f"Expected {expected}, got {cs}"
    
    # Test partial coherence
    cs_partial = btc_to_cs_conversion(btc, psi=0.5)
    expected_partial = 1.0 * 2.5773 * 0.5
    assert abs(cs_partial - expected_partial) < 1e-6, \
        f"Expected {expected_partial}, got {cs_partial}"
    
    # Test multiple BTC
    btc_multi = 5.0
    cs_multi = btc_to_cs_conversion(btc_multi)
    expected_multi = 5.0 * 2.5773
    assert abs(cs_multi - expected_multi) < 1e-6, \
        f"Expected {expected_multi}, got {cs_multi}"
    
    print("✓ Conversion formula test passed")


def test_verification():
    """Test the verification function."""
    result = verify_gap3_closure()
    
    assert "all_checks_passed" in result
    assert "details" in result
    assert "certificate" in result
    assert "status" in result
    
    # All checks should pass
    assert result["all_checks_passed"] == True, \
        f"Verification failed: {result['details']}"
    
    print("✓ Verification test passed")


def test_seal():
    """Test the seal is correctly set."""
    seal = GAP_3_CERTIFICATE["result"]["seal"]
    assert seal == "∴𓂀Ω∞³", f"Expected seal '∴𓂀Ω∞³', got '{seal}'"
    print("✓ Seal test passed")


def test_psi_values():
    """Test that ψ values are in expected range."""
    result = GAP_3_CERTIFICATE["result"]
    
    psi_initial = result["psi_initial"]
    psi_final = result["psi_final"]
    
    assert 0 < psi_initial < 1, f"Invalid psi_initial: {psi_initial}"
    assert psi_final == 1.0, f"Expected psi_final = 1.0, got {psi_final}"
    assert psi_initial < psi_final, "psi should increase"
    
    print("✓ Ψ values test passed")


def run_all_tests():
    """Run all tests."""
    print("\n" + "=" * 60)
    print("Running Gap 3 Certification Tests")
    print("=" * 60 + "\n")
    
    tests = [
        test_kappa_pi_constant,
        test_certificate_structure,
        test_constants,
        test_conversion_formula,
        test_verification,
        test_seal,
        test_psi_values
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__} failed: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} error: {e}")
            failed += 1
    
    print("\n" + "=" * 60)
    print(f"Tests passed: {passed}/{len(tests)}")
    print(f"Tests failed: {failed}/{len(tests)}")
    print("=" * 60 + "\n")
    
    if failed == 0:
        print("✅ All tests PASSED!\n")
        return 0
    else:
        print("❌ Some tests FAILED!\n")
        return 1


if __name__ == "__main__":
    exit_code = run_all_tests()
    sys.exit(exit_code)
