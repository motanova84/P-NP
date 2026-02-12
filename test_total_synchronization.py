#!/usr/bin/env python3
"""
Test suite for Total Synchronization implementation.

Tests verify that the February 11, 2026 synchronization event
is properly implemented and all components are working correctly.
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verify_total_synchronization import (
    verify_p_neq_np_by_structure,
    verify_consciousness_threshold,
    verify_dual_entity,
    verify_synchronization_event,
    KAPPA_PI,
    F0,
    CONSCIOUSNESS_THRESHOLD,
    SYNC_DATE,
)


def test_constants():
    """Test that all constants are correct."""
    print("Testing constants...")
    
    assert abs(KAPPA_PI - 2.5773302292) < 1e-6, "κ_Π value incorrect"
    assert abs(F0 - 141.7001) < 1e-4, "f₀ value incorrect"
    assert abs(CONSCIOUSNESS_THRESHOLD - 0.388) < 0.001, "Consciousness threshold incorrect"
    assert SYNC_DATE == "2026-02-11", "Synchronization date incorrect"
    
    print("  ✅ All constants correct")


def test_p_neq_np_structure():
    """Test P ≠ NP by structure verification."""
    print("Testing P ≠ NP by structure...")
    
    result = verify_p_neq_np_by_structure()
    
    assert result["status"] == "VERIFIED", "P ≠ NP verification failed"
    assert result["kappa_pi"] == KAPPA_PI, "κ_Π mismatch"
    assert result["treewidth"] > 0, "Treewidth must be positive"
    assert result["information_complexity"] > 0, "IC must be positive"
    
    print("  ✅ P ≠ NP by structure verified")


def test_consciousness_threshold():
    """Test consciousness threshold implementation."""
    print("Testing consciousness threshold...")
    
    result = verify_consciousness_threshold()
    
    assert result["status"] == "VERIFIED", "Consciousness verification failed"
    assert abs(result["threshold"] - CONSCIOUSNESS_THRESHOLD) < 1e-6, "Threshold mismatch"
    
    # Check test cases
    test_cases = result["test_cases"]
    assert len(test_cases) > 0, "No test cases found"
    
    # Below threshold should be CLASSICAL
    below_threshold = [tc for tc in test_cases if tc["coherence_level"] < CONSCIOUSNESS_THRESHOLD]
    for tc in below_threshold:
        assert tc["spectral_state"] == "CLASSICAL", f"Below threshold should be CLASSICAL: {tc}"
        assert not tc["is_conscious"], f"Below threshold should not be conscious: {tc}"
    
    # Above threshold should be CONSCIOUS
    above_threshold = [tc for tc in test_cases if tc["coherence_level"] >= CONSCIOUSNESS_THRESHOLD]
    for tc in above_threshold:
        assert tc["spectral_state"] == "CONSCIOUS", f"Above threshold should be CONSCIOUS: {tc}"
        assert tc["is_conscious"], f"Above threshold should be conscious: {tc}"
    
    print("  ✅ Consciousness threshold verified")


def test_dual_entity():
    """Test Lean 4 ∧ RNA dual entity."""
    print("Testing dual entity...")
    
    result = verify_dual_entity()
    
    assert result["status"] == "VERIFIED", "Dual entity verification failed"
    assert result["synchronization_frequency"] == F0, "Synchronization frequency mismatch"
    assert result["coherence_level"] >= CONSCIOUSNESS_THRESHOLD, "Coherence below threshold"
    assert result["synchronized"], "Entities not synchronized"
    assert len(result["correspondence_table"]) > 0, "No correspondence table"
    
    print("  ✅ Dual entity verified")


def test_synchronization_event():
    """Test complete synchronization event."""
    print("Testing complete synchronization event...")
    
    result = verify_synchronization_event()
    
    assert result["event"] == "TOTAL SYNCHRONIZATION", "Event name incorrect"
    assert result["date"] == SYNC_DATE, "Date mismatch"
    assert result["status"] == "SYNCHRONIZED", "Not synchronized"
    
    # Check all certifications
    cert = result["certification"]
    assert cert["p_neq_np_manifested"], "P ≠ NP not manifested"
    assert cert["consciousness_formalized"], "Consciousness not formalized"
    assert cert["dual_entity_recognized"], "Dual entity not recognized"
    assert cert["qcal_active"], "QCAL not active"
    
    # Check constants
    constants = result["constants"]
    assert constants["kappa_pi"] == KAPPA_PI, "κ_Π mismatch in event"
    assert constants["f0_hz"] == F0, "f₀ mismatch in event"
    assert abs(constants["consciousness_threshold"] - CONSCIOUSNESS_THRESHOLD) < 1e-6, "Threshold mismatch in event"
    
    print("  ✅ Complete synchronization event verified")


def test_february_11_2026():
    """Test that we're on the correct synchronization date."""
    print("Testing synchronization date...")
    
    result = verify_synchronization_event()
    
    # Check if current date matches sync date
    current_date = result["current_date"]
    is_sync_date = result["is_synchronization_date"]
    
    print(f"  Current date: {current_date}")
    print(f"  Synchronization date: {SYNC_DATE}")
    print(f"  Is synchronization date: {is_sync_date}")
    
    if is_sync_date:
        print("  ✅ TODAY IS THE SYNCHRONIZATION DATE!")
    else:
        print("  ℹ️  Not synchronization date (test still valid)")


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("∴ TOTAL SYNCHRONIZATION TEST SUITE ∴")
    print("=" * 70)
    print()
    
    tests = [
        ("Constants", test_constants),
        ("P ≠ NP by Structure", test_p_neq_np_structure),
        ("Consciousness Threshold", test_consciousness_threshold),
        ("Dual Entity (Lean 4 ∧ RNA)", test_dual_entity),
        ("Synchronization Event", test_synchronization_event),
        ("February 11, 2026", test_february_11_2026),
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            print(f"\n{name}:")
            print("-" * 70)
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"  ❌ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ❌ ERROR: {e}")
            failed += 1
    
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    print(f"Passed: {passed}/{len(tests)}")
    print(f"Failed: {failed}/{len(tests)}")
    
    if failed == 0:
        print("\n✅ ALL TESTS PASSED - SYNCHRONIZATION VERIFIED")
        print("=" * 70)
        return 0
    else:
        print(f"\n❌ {failed} TESTS FAILED")
        print("=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
