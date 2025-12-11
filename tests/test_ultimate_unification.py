#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Test suite for Ultimate Unification components

Tests the integration of empirical evidence, JSON certificate,
and validation tools.

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import json
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def test_certificate_exists():
    """Test that certificate file exists"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    assert cert_path.exists(), "Certificate file not found"
    print("✓ Certificate file exists")


def test_certificate_loads():
    """Test that certificate is valid JSON"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    assert cert is not None, "Certificate failed to load"
    print("✓ Certificate loads as valid JSON")


def test_certificate_structure():
    """Test that certificate has required sections"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    required_sections = [
        'metadata', 'constants', 'verifications', 'simulations',
        'proofs', 'experimental_certificate', 'integration'
    ]
    
    for section in required_sections:
        assert section in cert, f"Missing section: {section}"
    
    print("✓ Certificate has all required sections")


def test_constants_values():
    """Test that constants have correct values"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    constants = cert['constants']
    
    # Check κ_Π
    assert 'kappa_pi' in constants
    kappa_pi = constants['kappa_pi']['value']
    assert abs(kappa_pi - 2.5773) < 0.001, f"κ_Π value incorrect: {kappa_pi}"
    
    # Check f₀
    assert 'f_0' in constants
    f0 = constants['f_0']['value']
    assert abs(f0 - 141.7001) < 1.0, f"f₀ value incorrect: {f0}"
    
    # Check A_eff_max
    assert 'A_eff_max' in constants
    a_eff = constants['A_eff_max']['value']
    assert a_eff > 1.0, f"A_eff_max value incorrect: {a_eff}"
    
    # Check consciousness_threshold
    assert 'consciousness_threshold' in constants
    threshold = constants['consciousness_threshold']['value']
    assert threshold > 0.3, f"Threshold value incorrect: {threshold}"
    
    print("✓ All constants have correct values")


def test_threshold_crossed():
    """Test that threshold condition is met"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    constants = cert['constants']
    a_eff = constants['A_eff_max']['value']
    threshold = constants['consciousness_threshold']['value']
    
    assert a_eff >= threshold, \
        f"Threshold not crossed: {a_eff} < {threshold}"
    
    ratio = a_eff / threshold
    assert ratio > 2.0, \
        f"Threshold not significantly exceeded: ratio={ratio}"
    
    print(f"✓ Threshold crossed: {a_eff} ≥ {threshold} (ratio: {ratio:.4f})")


def test_verifications_passed():
    """Test that all verifications passed"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    verifications = cert['verifications']
    
    for name, data in verifications.items():
        assert data['passed'], f"Verification failed: {name}"
    
    print(f"✓ All {len(verifications)} verifications passed")


def test_proofs_status():
    """Test that proofs have valid status"""
    cert_path = Path(__file__).parent.parent / "ultimate_unification.json"
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    proofs = cert['proofs']
    
    valid_statuses = ['EMPIRICALLY_SUPPORTED', 'VERIFIED', 'ESTABLISHED', 'COMPLETE']
    
    for name, data in proofs.items():
        assert 'status' in data, f"Proof missing status: {name}"
        assert data['status'] in valid_statuses, \
            f"Invalid proof status: {name} = {data['status']}"
    
    print(f"✓ All {len(proofs)} proofs have valid status")


def test_lean_files_exist():
    """Test that Lean files exist"""
    base_path = Path(__file__).parent.parent
    
    lean_files = [
        'empirical_evidence.lean',
        'Ultimate_Unification.lean'
    ]
    
    for filename in lean_files:
        filepath = base_path / filename
        assert filepath.exists(), f"Lean file not found: {filename}"
    
    print(f"✓ All {len(lean_files)} Lean files exist")


def test_lean_files_have_content():
    """Test that Lean files have expected content"""
    base_path = Path(__file__).parent.parent
    
    # Check empirical_evidence.lean
    emp_path = base_path / 'empirical_evidence.lean'
    with open(emp_path, 'r') as f:
        emp_content = f.read()
    
    assert 'κ_Π_empirical' in emp_content
    assert 'consciousness_threshold' in emp_content
    assert 'BiologicalSystem' in emp_content
    assert 'EmpiricalEvidence' in emp_content
    
    # Check Ultimate_Unification.lean
    ult_path = base_path / 'Ultimate_Unification.lean'
    with open(ult_path, 'r') as f:
        ult_content = f.read()
    
    assert 'P_neq_NP_iff_consciousness_quantized_verified' in ult_content
    assert 'empirical_evidence_supports_P_neq_NP' in ult_content
    assert 'empirical_theoretical_bridge' in ult_content
    assert 'ExperimentalCertificate' in ult_content
    
    print("✓ Lean files contain expected definitions")


def test_lakefile_updated():
    """Test that lakefile includes new modules"""
    base_path = Path(__file__).parent.parent
    lakefile_path = base_path / 'lakefile.lean'
    
    with open(lakefile_path, 'r') as f:
        lakefile_content = f.read()
    
    assert 'EmpiricalEvidence' in lakefile_content
    assert 'UltimateUnification' in lakefile_content
    
    print("✓ lakefile.lean updated with new modules")


def test_documentation_exists():
    """Test that documentation files exist"""
    base_path = Path(__file__).parent.parent
    
    docs = [
        'ULTIMATE_UNIFICATION_README.md',
        'validate_certificate.py',
        'demo_ultimate_unification.py'
    ]
    
    for filename in docs:
        filepath = base_path / filename
        assert filepath.exists(), f"Documentation file not found: {filename}"
    
    print(f"✓ All {len(docs)} documentation files exist")


def run_all_tests():
    """Run all tests"""
    print()
    print("=" * 80)
    print("ULTIMATE UNIFICATION TEST SUITE")
    print("=" * 80)
    print()
    
    tests = [
        test_certificate_exists,
        test_certificate_loads,
        test_certificate_structure,
        test_constants_values,
        test_threshold_crossed,
        test_verifications_passed,
        test_proofs_status,
        test_lean_files_exist,
        test_lean_files_have_content,
        test_lakefile_updated,
        test_documentation_exists
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__}: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__}: Unexpected error: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 80)
    print()
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
