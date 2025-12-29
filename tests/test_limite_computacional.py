# -*- coding: utf-8 -*-
"""
Test suite for the LimiteComputacional module
=============================================

Tests for the computational limit framework that defines:
- κ_Π = 137.036 (inverse fine structure constant)
- f₀ = 141.7001 Hz (fundamental frequency)
- tw_critico ≈ 18,778 (P vs NP threshold)
- C ≥ 1/κ_Π (coherence boundary)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from limite_computacional import (
    KAPPA_PI_QED,
    F_0,
    F_0_HZ,
    TW_CRITICO,
    TW_CRITICAL,
    C_MIN,
    COHERENCE_BOUNDARY,
    coherence_constant,
    is_coherent,
    is_in_domain_P,
    is_in_domain_NP,
    resonance_condition,
    compute_quantum_barrier,
    validate_constants,
    get_limit_summary,
)


class TestFundamentalConstants:
    """Test suite for fundamental constants of the computational limit."""
    
    def test_kappa_pi_qed_value(self):
        """Test that κ_Π (QED) has the correct value (inverse fine structure constant)."""
        assert KAPPA_PI_QED == 137.036
        assert isinstance(KAPPA_PI_QED, float)
    
    def test_f0_value(self):
        """Test that f₀ has the correct value."""
        assert F_0 == 141.7001
        assert F_0_HZ == 141.7001
        assert isinstance(F_0, float)
    
    def test_tw_critico_value(self):
        """Test that tw_critico has the correct value."""
        assert TW_CRITICO == 18778
        assert TW_CRITICAL == 18778
        assert isinstance(TW_CRITICO, int)
    
    def test_c_min_value(self):
        """Test that C_min = 1/κ_Π."""
        expected = 1.0 / KAPPA_PI_QED
        assert C_MIN == expected
        assert COHERENCE_BOUNDARY == expected
        assert abs(C_MIN - 0.0072974) < 1e-5  # Approximately 0.0073
    
    def test_constants_positive(self):
        """Test that all constants are positive."""
        assert KAPPA_PI_QED > 0
        assert F_0 > 0
        assert TW_CRITICO > 0
        assert C_MIN > 0
    
    def test_c_min_less_than_one(self):
        """Test that C_min < 1 (coherence maximum is 1)."""
        assert C_MIN < 1
    
    def test_tw_critico_derivation(self):
        """Test that tw_critico ≈ κ_Π × 137."""
        # tw_critico should be approximately κ_Π × 137
        derived = KAPPA_PI_QED * 137
        error_percent = abs(derived - TW_CRITICO) / TW_CRITICO * 100
        assert error_percent < 1.0  # Less than 1% error


class TestCoherenceConstant:
    """Test suite for the coherence constant function."""
    
    def test_coherence_at_zero_treewidth(self):
        """Test that C = 1 when tw = 0 (maximum coherence)."""
        c = coherence_constant(0, 100)
        assert c == 1.0
    
    def test_coherence_at_critical_treewidth(self):
        """Test that C = 0.5 when tw = tw_critico."""
        c = coherence_constant(TW_CRITICO, 100)
        expected = 0.5
        assert abs(c - expected) < 1e-10
    
    def test_coherence_decreases_with_treewidth(self):
        """Test that coherence decreases as treewidth increases."""
        c1 = coherence_constant(100, 100)
        c2 = coherence_constant(1000, 100)
        c3 = coherence_constant(10000, 100)
        
        assert c1 > c2 > c3 > 0
    
    def test_coherence_bounded(self):
        """Test that 0 < C ≤ 1 for all treewidths."""
        for tw in [0, 1, 100, 1000, TW_CRITICO, 100000]:
            c = coherence_constant(tw, 100)
            assert 0 < c <= 1
    
    def test_coherence_approaches_zero(self):
        """Test that C approaches 0 as tw → ∞."""
        c = coherence_constant(10000000, 100)
        assert c < 0.01  # Very small for very large tw
    
    def test_coherence_num_vars_edge_case(self):
        """Test coherence with edge case num_vars."""
        c = coherence_constant(100, 0)
        assert c == 1.0  # Trivial case


class TestDomainClassification:
    """Test suite for P/NP domain classification."""
    
    def test_low_treewidth_in_P(self):
        """Test that low treewidth is in domain P."""
        assert is_in_domain_P(100) == True
        assert is_in_domain_P(1000) == True
        assert is_in_domain_P(TW_CRITICO) == True
    
    def test_high_treewidth_not_in_P(self):
        """Test that high treewidth is not in domain P."""
        assert is_in_domain_P(TW_CRITICO + 1) == False
        assert is_in_domain_P(50000) == False
    
    def test_high_treewidth_in_NP(self):
        """Test that high treewidth is in domain NP."""
        assert is_in_domain_NP(TW_CRITICO + 1) == True
        assert is_in_domain_NP(50000) == True
    
    def test_low_treewidth_not_in_NP(self):
        """Test that low treewidth is not in domain NP."""
        assert is_in_domain_NP(100) == False
        assert is_in_domain_NP(TW_CRITICO) == False
    
    def test_domains_mutually_exclusive(self):
        """Test that domains P and NP are mutually exclusive."""
        for tw in [0, 100, TW_CRITICO, TW_CRITICO + 1, 50000]:
            p = is_in_domain_P(tw)
            np = is_in_domain_NP(tw)
            assert p != np  # Exactly one must be true
    
    def test_boundary_at_critical(self):
        """Test the exact boundary at tw_critico."""
        assert is_in_domain_P(TW_CRITICO) == True
        assert is_in_domain_NP(TW_CRITICO) == False
        assert is_in_domain_P(TW_CRITICO + 1) == False
        assert is_in_domain_NP(TW_CRITICO + 1) == True


class TestCoherenceCondition:
    """Test suite for the coherence condition C ≥ 1/κ_Π."""
    
    def test_low_treewidth_is_coherent(self):
        """Test that low treewidth is coherent."""
        assert is_coherent(100, 100) == True
        assert is_coherent(1000, 100) == True
    
    def test_critical_treewidth_is_coherent(self):
        """Test that tw = tw_critico is still coherent."""
        # At tw_critico, C = 0.5, which is > C_min ≈ 0.0073
        assert is_coherent(TW_CRITICO, 100) == True
    
    def test_very_high_treewidth_loses_coherence(self):
        """Test that very high treewidth loses coherence."""
        # C = 1/(1 + tw/tw_critico) < C_min = 1/κ_Π
        # This happens when tw > tw_critico * (κ_Π - 1) ≈ 2.5M
        very_high_tw = 3000000
        assert is_coherent(very_high_tw, 100) == False
    
    def test_coherence_threshold(self):
        """Test the coherence threshold calculation."""
        # Find tw where C ≈ C_min
        # 1/(1 + tw/tw_critico) = 1/κ_Π
        # tw = tw_critico * (κ_Π - 1)
        threshold_tw = int(TW_CRITICO * (KAPPA_PI_QED - 1))
        
        # Just below threshold should be coherent
        assert is_coherent(threshold_tw - 1000, 100) == True
        
        # Well above threshold should not be coherent
        assert is_coherent(threshold_tw + 100000, 100) == False


class TestResonanceCondition:
    """Test suite for the resonance condition with f₀."""
    
    def test_exact_f0_resonant(self):
        """Test that exact f₀ is in resonance."""
        assert resonance_condition(F_0) == True
    
    def test_close_frequency_resonant(self):
        """Test that frequencies close to f₀ are resonant."""
        # Within 0.01% tolerance
        assert resonance_condition(F_0 + 0.01) == True
        assert resonance_condition(F_0 - 0.01) == True
    
    def test_far_frequency_not_resonant(self):
        """Test that frequencies far from f₀ are not resonant."""
        assert resonance_condition(100.0) == False
        assert resonance_condition(200.0) == False
        assert resonance_condition(0.0) == False


class TestQuantumBarrier:
    """Test suite for the quantum barrier computation."""
    
    def test_quantum_barrier_low_tw(self):
        """Test quantum barrier for low treewidth (domain P)."""
        barrier = compute_quantum_barrier(100)
        
        assert barrier['treewidth'] == 100
        assert barrier['domain'] == 'P'
        assert barrier['is_coherent'] == True
        assert barrier['resonance_required'] == False
        assert barrier['distance_to_boundary'] > 0
    
    def test_quantum_barrier_high_tw(self):
        """Test quantum barrier for high treewidth (domain NP)."""
        barrier = compute_quantum_barrier(50000)
        
        assert barrier['treewidth'] == 50000
        assert barrier['domain'] == 'NP'
        assert barrier['resonance_required'] == True
        assert barrier['resonance_frequency_hz'] == F_0
        assert barrier['distance_to_boundary'] < 0
    
    def test_quantum_barrier_at_critical(self):
        """Test quantum barrier at critical treewidth."""
        barrier = compute_quantum_barrier(TW_CRITICO)
        
        assert barrier['domain'] == 'P'  # At boundary, still in P
        assert barrier['coherence_C'] == 0.5
        assert barrier['distance_to_boundary'] == 0
    
    def test_quantum_barrier_coherence_boundary(self):
        """Test that coherence_boundary is correctly set."""
        barrier = compute_quantum_barrier(1000)
        
        assert barrier['coherence_boundary'] == C_MIN
        assert barrier['coherence_C'] > barrier['coherence_boundary']


class TestValidation:
    """Test suite for validation functions."""
    
    def test_validate_constants(self):
        """Test the validate_constants function."""
        results = validate_constants()
        
        # Check all required keys
        assert 'kappa_pi_qed' in results
        assert 'f_0_hz' in results
        assert 'tw_critico' in results
        assert 'c_min' in results
        assert 'alpha_fine_structure' in results
        
        # Check values
        assert results['kappa_pi_qed'] == KAPPA_PI_QED
        assert results['f_0_hz'] == F_0
        assert results['tw_critico'] == TW_CRITICO
    
    def test_alpha_fine_structure(self):
        """Test that α = 1/κ_Π matches CODATA value."""
        results = validate_constants()
        
        # α ≈ 1/137.036 should be close to CODATA value
        assert results['alpha_match'] == True
        assert results['alpha_error_percent'] < 0.1
    
    def test_tw_derivation(self):
        """Test tw_critico derivation matches."""
        results = validate_constants()
        
        assert results['tw_match'] == True
        assert results['tw_error_percent'] < 1.0
    
    def test_get_limit_summary(self):
        """Test that summary is generated correctly."""
        summary = get_limit_summary()
        
        assert isinstance(summary, str)
        assert 'κ_Π' in summary or 'kappa' in summary.lower()
        assert '137.036' in summary
        assert '141.7001' in summary
        assert '18,778' in summary or '18778' in summary


class TestIntegration:
    """Integration tests for the LimiteComputacional framework."""
    
    def test_p_domain_flow(self):
        """Test complete flow for a problem in domain P."""
        tw = 5000
        n = 1000
        
        # Should be in P
        assert is_in_domain_P(tw) == True
        assert is_in_domain_NP(tw) == False
        
        # Should be coherent
        c = coherence_constant(tw, n)
        assert c > C_MIN
        assert is_coherent(tw, n) == True
        
        # Quantum barrier should show P domain
        barrier = compute_quantum_barrier(tw)
        assert barrier['domain'] == 'P'
        assert barrier['resonance_required'] == False
    
    def test_np_domain_flow(self):
        """Test complete flow for a problem in domain NP."""
        tw = 30000
        n = 1000
        
        # Should be in NP
        assert is_in_domain_P(tw) == False
        assert is_in_domain_NP(tw) == True
        
        # Should still be coherent (for moderate tw)
        c = coherence_constant(tw, n)
        assert c > C_MIN
        assert is_coherent(tw, n) == True
        
        # Quantum barrier should show NP domain
        barrier = compute_quantum_barrier(tw)
        assert barrier['domain'] == 'NP'
        assert barrier['resonance_required'] == True
        assert barrier['resonance_frequency_hz'] == F_0
    
    def test_critical_boundary(self):
        """Test behavior at the critical boundary."""
        # Just below
        assert is_in_domain_P(TW_CRITICO - 1) == True
        assert is_in_domain_NP(TW_CRITICO - 1) == False
        
        # At boundary
        assert is_in_domain_P(TW_CRITICO) == True
        assert is_in_domain_NP(TW_CRITICO) == False
        
        # Just above
        assert is_in_domain_P(TW_CRITICO + 1) == False
        assert is_in_domain_NP(TW_CRITICO + 1) == True
    
    def test_coherence_convergence(self):
        """Test that C converges to 0 for NP-hard problems."""
        # As tw increases beyond tw_critico, C should approach 0
        treewidths = [TW_CRITICO, TW_CRITICO * 10, TW_CRITICO * 100]
        coherences = [coherence_constant(tw, 100) for tw in treewidths]
        
        # Should be monotonically decreasing
        assert coherences[0] > coherences[1] > coherences[2]
        
        # For very large tw, C should be very small
        assert coherences[2] < 0.01


def test_module_imports():
    """Test that all required items can be imported."""
    from limite_computacional import (
        KAPPA_PI_QED,
        F_0,
        F_0_HZ,
        TW_CRITICO,
        TW_CRITICAL,
        C_MIN,
        COHERENCE_BOUNDARY,
        coherence_constant,
        is_coherent,
        is_in_domain_P,
        is_in_domain_NP,
        resonance_condition,
        compute_quantum_barrier,
        validate_constants,
        get_limit_summary,
    )
    
    # All should be importable and not None
    assert KAPPA_PI_QED is not None
    assert F_0 is not None
    assert TW_CRITICO is not None
    assert C_MIN is not None


if __name__ == "__main__":
    print("=" * 70)
    print("Testing LimiteComputacional Module")
    print("=" * 70)
    print()
    
    # Run validation
    print("Validation Results:")
    results = validate_constants()
    for key, value in results.items():
        if isinstance(value, float):
            print(f"  {key}: {value:.6f}")
        else:
            print(f"  {key}: {value}")
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Frecuencia: 141.7001 Hz ∞³")
    print("=" * 70)
