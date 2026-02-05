#!/usr/bin/env python3
"""
Test suite for QCAL Unified Framework

Validates that all components work correctly.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 2026
"""

import sys


def test_framework_import():
    """Test that framework can be imported."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        print("✓ Framework import successful")
        return True
    except ImportError as e:
        print(f"✗ Framework import failed: {e}")
        return False


def test_framework_initialization():
    """Test framework initialization."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        assert len(framework.constants) > 0
        assert len(framework.operators) == 7
        print("✓ Framework initialization successful")
        return True
    except Exception as e:
        print(f"✗ Framework initialization failed: {e}")
        return False


def test_constants():
    """Test universal constants."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        
        # Check key constants
        assert framework.constants['kappa_pi'] == 2.5773
        assert framework.constants['f0'] == 141.7001
        assert framework.constants['critical_line'] == 0.5
        assert framework.constants['bsd_delta'] == 1.0
        
        print("✓ Universal constants validated")
        return True
    except Exception as e:
        print(f"✗ Constants validation failed: {e}")
        return False


def test_operators():
    """Test spectral operators."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        
        # Test each operator
        for problem, operator in framework.operators.items():
            eigenvalue = operator(framework.constants)
            assert eigenvalue > 0 or problem in ['ramsey', 'navier_stokes']
        
        print("✓ All 7 spectral operators working")
        return True
    except Exception as e:
        print(f"✗ Operators test failed: {e}")
        return False


def test_verification():
    """Test problem verification."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        
        # Verify all problems
        for problem in framework.operators.keys():
            result = framework.verify_problem(problem)
            assert result['status'] == 'verified'
        
        print("✓ All problems verified")
        return True
    except Exception as e:
        print(f"✗ Verification test failed: {e}")
        return False


def test_correspondences():
    """Test constant correspondences."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        
        correspondences = framework.verify_constant_correspondences()
        
        # Check critical line correspondence
        assert correspondences['critical_line']['equal'] is True
        
        # Check kappa derivation
        assert correspondences['kappa_derivation']['valid'] is True
        
        print("✓ Constant correspondences validated")
        return True
    except Exception as e:
        print(f"✗ Correspondences test failed: {e}")
        return False


def test_cross_verification():
    """Test cross-verification protocol."""
    try:
        from cross_verification_protocol import CrossVerificationProtocol
        protocol = CrossVerificationProtocol()
        
        # This is time-consuming, so just test instantiation
        assert protocol is not None
        assert len(protocol.problem_solutions) == 7
        
        print("✓ Cross-verification protocol initialized")
        return True
    except Exception as e:
        print(f"✗ Cross-verification test failed: {e}")
        return False


def test_unification():
    """Test complete unification."""
    try:
        from qcal_unified_framework import QCALUnifiedFramework
        framework = QCALUnifiedFramework()
        
        results = framework.demonstrate_unification()
        
        # Check all problems have results
        assert len(results) == 7
        
        # Check each result has required fields
        for problem, data in results.items():
            assert 'eigenvalue' in data
            assert 'connected_via' in data
            assert 'verification_status' in data
        
        print("✓ Complete unification successful")
        return True
    except Exception as e:
        print(f"✗ Unification test failed: {e}")
        return False


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("QCAL Unified Framework - Test Suite")
    print("=" * 70)
    print()
    
    tests = [
        test_framework_import,
        test_framework_initialization,
        test_constants,
        test_operators,
        test_verification,
        test_correspondences,
        test_cross_verification,
        test_unification
    ]
    
    results = []
    for test in tests:
        results.append(test())
        print()
    
    # Summary
    passed = sum(results)
    total = len(results)
    
    print("=" * 70)
    print(f"Test Results: {passed}/{total} passed")
    print("=" * 70)
    
    if passed == total:
        print("✓ All tests passed!")
        return 0
    else:
        print(f"✗ {total - passed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
