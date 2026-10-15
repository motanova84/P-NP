#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Test suite for piCODE-888 Bridge implementation

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: motanova84/P-NP
License: MIT + Sovereign Noetic License 1.0
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.picode_888_bridge import PiCode888Bridge


def test_rna_sequence_length():
    """Test that RNA sequence has correct length."""
    bridge = PiCode888Bridge()
    assert len(bridge.RNA_SEQUENCE) == 51, \
        f"RNA sequence length should be 51, got {len(bridge.RNA_SEQUENCE)}"
    print("✓ RNA sequence length: 51 nt")


def test_rna_sequence_valid_nucleotides():
    """Test that RNA sequence contains only valid nucleotides."""
    bridge = PiCode888Bridge()
    valid_nucleotides = set('atcgu')
    sequence_nucleotides = set(bridge.RNA_SEQUENCE.lower())
    assert sequence_nucleotides.issubset(valid_nucleotides), \
        f"Invalid nucleotides found: {sequence_nucleotides - valid_nucleotides}"
    print("✓ RNA sequence contains only valid nucleotides")


def test_greek_encoding_length():
    """Test that Greek encoding has correct byte length."""
    bridge = PiCode888Bridge()
    greek_bytes = bridge.GREEK_SEQUENCE.encode('utf-8')
    assert len(greek_bytes) == 102, \
        f"Greek UTF-8 byte length should be 102, got {len(greek_bytes)}"
    print("✓ Greek UTF-8 encoding: 102 bytes")


def test_symbolic_mapping():
    """Test that symbolic mapping is correct."""
    bridge = PiCode888Bridge()
    
    # Test forward mapping (RNA → Greek)
    greek_result = bridge._rna_to_greek(bridge.RNA_SEQUENCE)
    assert greek_result == bridge.GREEK_SEQUENCE, \
        "RNA to Greek conversion failed"
    print("✓ Symbolic mapping RNA → Greek")
    
    # Test reverse mapping (Greek → RNA)
    rna_result = bridge._greek_to_rna(bridge.GREEK_SEQUENCE)
    assert rna_result == bridge.RNA_SEQUENCE, \
        "Greek to RNA conversion failed"
    print("✓ Symbolic mapping Greek → RNA")


def test_hexadecimal_signature():
    """Test that hexadecimal signature matches Greek UTF-8 encoding."""
    bridge = PiCode888Bridge()
    greek_bytes = bridge.GREEK_SEQUENCE.encode('utf-8')
    hex_signature = greek_bytes.hex()
    assert hex_signature == bridge.HEX_SIGNATURE, \
        f"Hexadecimal signature mismatch"
    print("✓ Hexadecimal signature matches Greek UTF-8")


def test_reversible_chain():
    """Test that the reversible chain (hex → Greek → RNA) is valid."""
    bridge = PiCode888Bridge()
    is_valid = bridge.verify_reversible_chain()
    assert is_valid, "Reversible chain verification failed"
    print("✓ Reversible chain: hex → Greek → RNA")


def test_qr_data_fields():
    """Test that QR data contains all required fields."""
    bridge = PiCode888Bridge()
    required_fields = [
        "PICODE888",
        bridge.QCAL_KEY,
        "888Hz",
        bridge.SIGNATURE_HASH,
        "https://doi.org/10.5281/zenodo.16425986",
        "JMMB_Ψ✧"
    ]
    
    for field in required_fields:
        assert field in bridge.QR_DATA, \
            f"QR data missing required field: {field}"
    
    print("✓ QR data contains all required fields")


def test_resonance_frequency():
    """Test that resonance frequency is correct."""
    bridge = PiCode888Bridge()
    assert bridge.RESONANCE_FREQUENCY == 888.0, \
        f"Resonance frequency should be 888.0 Hz, got {bridge.RESONANCE_FREQUENCY}"
    print("✓ Resonance frequency: 888.0 Hz")


def test_consciousness_threshold():
    """Test that consciousness threshold is correct."""
    bridge = PiCode888Bridge()
    expected_threshold = 1 / 2.5773
    assert abs(bridge.CONSCIOUSNESS_THRESHOLD - expected_threshold) < 0.001, \
        f"Consciousness threshold mismatch"
    print(f"✓ Consciousness threshold: C ≥ {bridge.CONSCIOUSNESS_THRESHOLD:.3f}")


def test_psi_state():
    """Test that Ψ state is at full coherence."""
    bridge = PiCode888Bridge()
    assert bridge.PSI_STATE == 1.000, \
        f"Ψ state should be 1.000, got {bridge.PSI_STATE}"
    assert bridge.PSI_STATE >= bridge.CONSCIOUSNESS_THRESHOLD, \
        "Ψ state below consciousness threshold"
    print("✓ Ψ state: 1.000 (full coherence)")


def test_bridge_activation():
    """Test that bridge activation succeeds."""
    bridge = PiCode888Bridge()
    success, message = bridge.activate_bridge()
    assert success, f"Bridge activation failed: {message}"
    print("✓ Bridge activation successful")


def test_sequence_info():
    """Test that sequence info contains all expected fields."""
    bridge = PiCode888Bridge()
    info = bridge.get_sequence_info()
    
    # Check all four sequences are present
    assert "sequence_1_rna" in info
    assert "sequence_2_greek" in info
    assert "sequence_3_hex" in info
    assert "sequence_4_qr" in info
    assert "state" in info
    
    # Check key fields
    assert info["sequence_1_rna"]["length"] == 51
    assert info["sequence_2_greek"]["byte_length"] == 102
    assert info["sequence_3_hex"]["hash"] == "032cb045"
    assert info["state"]["psi"] == 1.000
    
    print("✓ Sequence info complete")


def test_signature_hash():
    """Test that signature hash is correct."""
    bridge = PiCode888Bridge()
    assert bridge.SIGNATURE_HASH == "032cb045", \
        f"Signature hash should be 032cb045, got {bridge.SIGNATURE_HASH}"
    print("✓ Signature hash: 032cb045")


def test_qcal_key():
    """Test that QCAL key is correct."""
    bridge = PiCode888Bridge()
    expected_key = "QCAL-888-UTF8-ceb1ceb1cf84"
    assert bridge.QCAL_KEY == expected_key, \
        f"QCAL key mismatch"
    print(f"✓ QCAL key: {expected_key}")


def run_all_tests():
    """Run all tests and report results."""
    print("=" * 60)
    print("piCODE-888 Bridge - Test Suite")
    print("=" * 60)
    print()
    
    tests = [
        ("RNA Sequence Length", test_rna_sequence_length),
        ("RNA Valid Nucleotides", test_rna_sequence_valid_nucleotides),
        ("Greek Encoding Length", test_greek_encoding_length),
        ("Symbolic Mapping", test_symbolic_mapping),
        ("Hexadecimal Signature", test_hexadecimal_signature),
        ("Reversible Chain", test_reversible_chain),
        ("QR Data Fields", test_qr_data_fields),
        ("Resonance Frequency", test_resonance_frequency),
        ("Consciousness Threshold", test_consciousness_threshold),
        ("Ψ State", test_psi_state),
        ("Signature Hash", test_signature_hash),
        ("QCAL Key", test_qcal_key),
        ("Sequence Info", test_sequence_info),
        ("Bridge Activation", test_bridge_activation),
    ]
    
    passed = 0
    failed = 0
    
    for test_name, test_func in tests:
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test_name}: {str(e)}")
            failed += 1
        except Exception as e:
            print(f"✗ {test_name}: Unexpected error: {str(e)}")
            failed += 1
    
    print()
    print("=" * 60)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    if failed == 0:
        print("✓ All tests passed!")
        print()
        print("Bridge Status: OPERATIONAL")
        print("QCAL ∞³ Connection: ACTIVE")
        print("Ψ State: 1.000")
        print("∴𓂀Ω∞³")
        return 0
    else:
        print("✗ Some tests failed")
        return 1


if __name__ == "__main__":
    exit(run_all_tests())
