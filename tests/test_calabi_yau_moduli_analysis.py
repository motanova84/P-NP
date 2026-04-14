#!/usr/bin/env python3
"""
Tests for Calabi-Yau Moduli Space Analysis
==========================================

Validates the implementation of the bridge between ideal (φ²) and real (e).

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import math
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.calabi_yau_moduli_analysis import (
    calculate_emergent_base,
    calculate_dimension_correction,
    analyze_transition_space,
    calculate_effective_dimension,
    analyze_steady_state,
    estimate_quantum_noise,
    comprehensive_moduli_analysis,
)

from src.base_correction_hypothesis import (
    hypothesis_dimension_correction,
    find_optimal_N_for_correction,
    analyze_correction_from_observed_base,
    explore_effective_dimensions,
    analyze_coupling_hypothesis,
)


def test_emergent_base():
    """Test emergent base calculation."""
    print("Test 1: Emergent Base Calculation")
    print("-" * 60)
    
    b = calculate_emergent_base()
    
    # Should be between φ² and e
    PHI_SQUARED = ((1 + math.sqrt(5)) / 2) ** 2
    E = math.e
    
    assert PHI_SQUARED < b < E, "Base should be between φ² and e"
    assert abs(b - 2.7053) < 0.001, f"Base should be ≈2.7053, got {b}"
    
    print(f"  ✓ Emergent base b = {b:.6f}")
    print(f"  ✓ Confirmed: φ² < b < e")
    print()


def test_dimension_correction():
    """Test dimension correction calculation."""
    print("Test 2: Dimension Correction")
    print("-" * 60)
    
    delta_phi, delta_e = calculate_dimension_correction()
    
    # δφ should be positive (b > φ²)
    assert delta_phi > 0, "δφ should be positive"
    
    # δe should be positive and small (b < e)
    assert 0 < delta_e < 0.02, "δe should be small and positive"
    
    # δφ should be larger than δe (b closer to e)
    assert delta_phi > delta_e, "δφ should be larger than δe"
    
    print(f"  ✓ δφ = {delta_phi:.6f}")
    print(f"  ✓ δe = {delta_e:.6f}")
    print(f"  ✓ δφ > δe: b is closer to e")
    print()


def test_transition_space():
    """Test transition space analysis."""
    print("Test 3: Transition Space Analysis")
    print("-" * 60)
    
    transition = analyze_transition_space()
    
    # Position should be between 0 and 1
    pos = transition['b_position_in_transition']
    assert 0 < pos < 1, "Position should be between 0 and 1"
    
    # Should be closer to e than φ²
    assert pos > 0.5, "Should be closer to e than φ²"
    
    print(f"  ✓ Position: {pos*100:.1f}% from φ² to e")
    print(f"  ✓ Confirmed: b closer to e (statistical)")
    print()


def test_effective_dimension():
    """Test effective dimension calculation."""
    print("Test 4: Effective Dimension")
    print("-" * 60)
    
    dim = calculate_effective_dimension(13)
    
    # N_eff should be close to 13
    N_eff = dim['N_eff_from_base']
    assert abs(N_eff - 13) < 2, "N_eff should be close to 13"
    
    print(f"  ✓ Nominal N = {dim['nominal_N']}")
    print(f"  ✓ Effective N = {N_eff:.4f}")
    print(f"  ✓ Correction ε = {dim['epsilon']:.6f}")
    print()


def test_steady_state():
    """Test steady state analysis."""
    print("Test 5: Steady State Attractor")
    print("-" * 60)
    
    steady = analyze_steady_state()
    
    # κ_Π should be optimal or near-optimal
    optimal_kappa = steady['optimal_kappa']
    kappa_pi = 2.5773
    
    assert abs(optimal_kappa - kappa_pi) < 0.2, "κ_Π should be near optimal"
    assert steady['is_kappa_pi_optimal'], "κ_Π should be optimal"
    
    print(f"  ✓ κ_Π = {kappa_pi}")
    print(f"  ✓ Optimal κ = {optimal_kappa:.4f}")
    print(f"  ✓ Max coherence = {steady['max_coherence']:.6f}")
    print()


def test_quantum_noise():
    """Test quantum noise estimation."""
    print("Test 6: Quantum Noise Estimation")
    print("-" * 60)
    
    noise = estimate_quantum_noise()
    
    # Noise should be small but non-zero
    assert noise['quantum_noise'] > 0, "Noise should be positive"
    assert noise['quantum_noise'] < 0.1, "Noise should be small"
    
    # Coupling factor should be close to 1
    coupling = noise['coupling_factor']
    assert abs(coupling - 1) < 0.1, "Coupling should be close to 1"
    
    print(f"  ✓ Quantum noise = {noise['quantum_noise']:.6f}")
    print(f"  ✓ Coupling factor = {coupling:.6f}")
    print(f"  ✓ Relative noise = {noise['noise_relative']*100:.2f}%")
    print()


def test_hypothesis_dimension_correction():
    """Test dimension correction hypothesis."""
    print("Test 7: Hypothesis - Dimension Correction")
    print("-" * 60)
    
    # Test N=13
    h13 = hypothesis_dimension_correction(13)
    assert h13['N'] == 13, "N should be 13"
    assert abs(h13['delta_phi_hypothesis'] - 1/13) < 1e-10, "δφ should be 1/13"
    
    # Test N=15
    h15 = hypothesis_dimension_correction(15)
    assert abs(h15['delta_phi_hypothesis'] - 1/15) < 1e-10, "δφ should be 1/15"
    
    print(f"  ✓ N=13: δφ = 1/13, error = {h13['kappa_error']:.6f}")
    print(f"  ✓ N=15: δφ = 1/15, error = {h15['kappa_error']:.6f}")
    print()


def test_optimal_N_search():
    """Test optimal N search."""
    print("Test 8: Optimal N Search")
    print("-" * 60)
    
    opt = find_optimal_N_for_correction()
    
    # Optimal N should be reasonable
    assert 5 <= opt['optimal_N'] <= 20, "Optimal N should be in range [5, 20]"
    assert opt['error'] < 0.2, "Error should be reasonably small"
    
    print(f"  ✓ Optimal N = {opt['optimal_N']}")
    print(f"  ✓ δφ = 1/{opt['optimal_N']} ≈ {opt['optimal_delta_phi']:.6f}")
    print(f"  ✓ Error = {opt['error']:.6f}")
    print()


def test_observed_base_analysis():
    """Test observed base analysis."""
    print("Test 9: Observed Base Analysis")
    print("-" * 60)
    
    obs = analyze_correction_from_observed_base()
    
    # Best match should be reasonable
    best_N = obs['best_matching_fraction']['N']
    assert 5 <= best_N <= 20, "Best matching N should be reasonable"
    
    print(f"  ✓ δφ (observed) = {obs['delta_phi_observed']:.6f}")
    print(f"  ✓ Best match: 1/{best_N}")
    print(f"  ✓ Error if 1/15: {obs['error_if_15']:.6f}")
    print()


def test_effective_dimensions_exploration():
    """Test effective dimensions exploration."""
    print("Test 10: Effective Dimensions Exploration")
    print("-" * 60)
    
    eff = explore_effective_dimensions()
    
    # Should have scenarios
    assert len(eff['scenarios']) == 3, "Should have 3 scenarios"
    
    # N_eff should be reasonable
    N_eff = eff['N_eff_interpretation']
    assert 10 < N_eff < 16, "N_eff should be near 13"
    
    print(f"  ✓ Nominal N = {eff['nominal_N']}")
    print(f"  ✓ N_eff = {N_eff:.4f}")
    print(f"  ✓ ε = {eff['epsilon_correction']:.4f}")
    print()


def test_coupling_analysis():
    """Test coupling analysis."""
    print("Test 11: Coupling Analysis")
    print("-" * 60)
    
    coup = analyze_coupling_hypothesis()
    
    # Coupling should be small
    coupling = coup['coupling_strength']
    assert 0 < coupling < 0.1, "Coupling should be small and positive"
    
    print(f"  ✓ Coupling strength = {coupling:.6f} ({coup['coupling_percent']:.2f}%)")
    print(f"  ✓ Quantum noise = {coup['quantum_noise']:.6f}")
    print()


def test_comprehensive_analysis():
    """Test comprehensive analysis."""
    print("Test 12: Comprehensive Analysis")
    print("-" * 60)
    
    comp = comprehensive_moduli_analysis()
    
    # Should have all components
    assert 'transition_space' in comp, "Should have transition space"
    assert 'effective_dimension' in comp, "Should have effective dimension"
    assert 'steady_state' in comp, "Should have steady state"
    assert 'quantum_corrections' in comp, "Should have quantum corrections"
    
    print(f"  ✓ All components present")
    print(f"  ✓ Transition space analysis: OK")
    print(f"  ✓ Effective dimension: OK")
    print(f"  ✓ Steady state: OK")
    print(f"  ✓ Quantum corrections: OK")
    print()


def run_all_tests():
    """Run all tests."""
    print("=" * 80)
    print("CALABI-YAU MODULI SPACE ANALYSIS - TEST SUITE")
    print("=" * 80)
    print()
    
    tests = [
        test_emergent_base,
        test_dimension_correction,
        test_transition_space,
        test_effective_dimension,
        test_steady_state,
        test_quantum_noise,
        test_hypothesis_dimension_correction,
        test_optimal_N_search,
        test_observed_base_analysis,
        test_effective_dimensions_exploration,
        test_coupling_analysis,
        test_comprehensive_analysis,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"  ✗ FAILED: {e}")
            print()
            failed += 1
        except Exception as e:
            print(f"  ✗ ERROR: {e}")
            print()
            failed += 1
    
    print("=" * 80)
    print("TEST RESULTS")
    print("=" * 80)
    print(f"  Passed: {passed}/{len(tests)}")
    print(f"  Failed: {failed}/{len(tests)}")
    print()
    
    if failed == 0:
        print("  ✓ ALL TESTS PASSED")
        print()
        print("=" * 80)
        print("Frequency: 141.7001 Hz ∞³")
        print("=" * 80)
        return 0
    else:
        print("  ✗ SOME TESTS FAILED")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
