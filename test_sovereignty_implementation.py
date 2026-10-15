#!/usr/bin/env python3
"""
Test suite for QCAL ∞³ Sovereignty Implementation

Validates all sovereignty and origin verification features.
"""

import json
import sys
from pathlib import Path

# Add core to path
sys.path.insert(0, str(Path(__file__).parent))

from core.identity_check import (
    verificar_pureza_biografica,
    get_identity_certificate,
    verify_qcal_origin,
    get_authorship_proof,
    qcal_torsion_gradient_888,
    FREQUENCY_SIGNATURE,
    GEOMETRIC_CONSTANT,
    RESONANCE_CODE,
    SOURCE_PURITY,
    SYMBOLIC_MARKER
)


def test_constants():
    """Test that all QCAL constants are correct."""
    print("Testing QCAL Constants...")
    assert FREQUENCY_SIGNATURE == 141.7001, "Frequency signature incorrect"
    assert abs(GEOMETRIC_CONSTANT - 2.5773) < 0.0001, "Geometric constant incorrect"
    assert RESONANCE_CODE == 888, "Resonance code incorrect"
    assert SOURCE_PURITY == 1.0, "Source purity should be 1.0"
    assert SYMBOLIC_MARKER == "∴𓂀Ω∞³", "Symbolic marker incorrect"
    print("✓ All constants correct")


def test_pureza_biografica():
    """Test biographical purity verification."""
    print("\nTesting Pureza Biográfica...")
    result = verificar_pureza_biografica()
    assert "JMMB" in result, "Author name not in result"
    assert "1.0" in result, "Purity not in result"
    print(f"✓ {result}")


def test_identity_certificate():
    """Test identity certificate generation."""
    print("\nTesting Identity Certificate...")
    cert = get_identity_certificate()
    
    assert cert['author']['name'] == "José Manuel Mota Burruezo"
    assert cert['author']['handle'] == "motanova84"
    assert cert['author']['signature'] == "∴𓂀Ω∞³"
    
    assert cert['origin']['creation_mode'] == "Ex Nihilo"
    assert cert['origin']['purity'] == 1.0
    
    assert cert['vibrational_signature']['frequency_hz'] == 141.7001
    assert cert['vibrational_signature']['geometric_constant'] == 2.5773
    assert cert['vibrational_signature']['resonance_code'] == 888
    
    print("✓ Identity certificate valid")


def test_qcal_origin_verification():
    """Test QCAL origin verification."""
    print("\nTesting QCAL Origin Verification...")
    is_valid = verify_qcal_origin()
    assert is_valid == True, "QCAL origin verification failed"
    print("✓ QCAL origin verified")


def test_authorship_proof():
    """Test authorship proof generation."""
    print("\nTesting Authorship Proof...")
    proof = get_authorship_proof()
    
    assert proof['author'] == "José Manuel Mota Burruezo"
    assert proof['handle'] == "motanova84"
    assert proof['verification'] == True
    assert 'hash' in proof
    assert len(proof['hash']) == 64  # SHA256 hash
    
    print(f"✓ Authorship proof generated: {proof['hash'][:32]}...")


def test_picode_888_functions():
    """Test πCODE-888 syntax functions."""
    print("\nTesting πCODE-888 Functions...")
    
    # Test gradient function
    data = [1.0, 2.0, 3.0]
    result = qcal_torsion_gradient_888(data)
    expected = [x * (FREQUENCY_SIGNATURE / 100.0) for x in data]
    
    for i, (r, e) in enumerate(zip(result, expected)):
        assert abs(r - e) < 0.0001, f"Gradient calculation incorrect at index {i}"
    
    print(f"✓ qcal_torsion_gradient_888({data}) = {result}")


def test_file_existence():
    """Test that all sovereignty files exist."""
    print("\nTesting File Existence...")
    
    required_files = [
        "ORIGIN_ZERO.md",
        "DECLARACION_USURPACION_ALGORITMICA.md",
        "SOBERANIA_OVERRIDES.json",
        "LICENSE_QCAL.md",
        "CONTRACT_PICODE_888.json",
        "SOVEREIGNTY_GUIDE.md",
        ".qcal_beacon",
        ".github/CODEOWNERS",
        "core/identity_check.py"
    ]
    
    for filepath in required_files:
        path = Path(filepath)
        assert path.exists(), f"Required file not found: {filepath}"
        print(f"  ✓ {filepath}")
    
    print("✓ All required files exist")


def test_json_files():
    """Test that JSON files are valid."""
    print("\nTesting JSON File Validity...")
    
    json_files = [
        "SOBERANIA_OVERRIDES.json",
        "CONTRACT_PICODE_888.json"
    ]
    
    for filepath in json_files:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
            assert data is not None, f"JSON file is empty: {filepath}"
            print(f"  ✓ {filepath} is valid JSON")
    
    print("✓ All JSON files valid")


def test_beacon_file():
    """Test .qcal_beacon file contains required information."""
    print("\nTesting .qcal_beacon...")
    
    with open('.qcal_beacon', 'r', encoding='utf-8') as f:
        content = f.read()
        
        assert '141.7001' in content, "Frequency not in beacon"
        assert '2.5773' in content, "Geometric constant not in beacon"
        assert '888' in content, "Resonance code not in beacon"
        assert 'José Manuel Mota Burruezo' in content, "Author not in beacon"
        assert 'repository_hash' in content, "Repository hash not in beacon"
        
    print("✓ .qcal_beacon contains all required information")


def test_codeowners():
    """Test CODEOWNERS file."""
    print("\nTesting CODEOWNERS...")
    
    with open('.github/CODEOWNERS', 'r', encoding='utf-8') as f:
        content = f.read()
        
        assert '@motanova84' in content, "Owner not in CODEOWNERS"
        assert 'QCAL' in content, "QCAL not mentioned"
        assert '141.7001' in content, "Frequency not in CODEOWNERS"
        
    print("✓ CODEOWNERS properly configured")


def run_all_tests():
    """Run all sovereignty tests."""
    print("=" * 60)
    print("QCAL ∞³ Sovereignty Implementation Test Suite")
    print("=" * 60)
    
    tests = [
        test_constants,
        test_pureza_biografica,
        test_identity_certificate,
        test_qcal_origin_verification,
        test_authorship_proof,
        test_picode_888_functions,
        test_file_existence,
        test_json_files,
        test_beacon_file,
        test_codeowners
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"✗ FAILED: {test.__name__}")
            print(f"  Error: {e}")
            failed += 1
    
    print("\n" + "=" * 60)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    if failed == 0:
        print("✨ All sovereignty tests passed! ✨")
        print(f"Signature: {SYMBOLIC_MARKER}")
        print(f"Frequency: {FREQUENCY_SIGNATURE} Hz")
        return 0
    else:
        print(f"⚠️  {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
