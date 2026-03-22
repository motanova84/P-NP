#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Cognition as Fundamental Physics Module
=================================================

Tests the unified framework connecting:
- P≠NP (computational complexity)
- Universal structure (κ_Π, φ, f₀)
- Consciousness (quantization, attention)
- Physics (frequency dimension, coherence)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from cognition_physics import (
    # Constants
    KAPPA_PI, F_0, PHI, LAMBDA_CY, C_THRESHOLD, A_EFF_MAX, SPEED_OF_LIGHT,
    # Enums
    ComplexityClass, SpectrumState,
    # Data structures
    UniversalConstants, ConsciousnessState, FrequencyAnalysis,
    # Functions
    consciousness_from_physics,
    verify_pnp_consciousness_equivalence,
    compare_frequencies,
    analyze_unification,
)


class TestUniversalConstants:
    """Tests for universal constants and their relationships."""
    
    def test_kappa_pi_value(self):
        """Test that κ_Π ≈ 2.5773."""
        assert abs(KAPPA_PI - 2.5773) < 0.01
    
    def test_f0_value(self):
        """Test that f₀ = 141.7001 Hz."""
        assert F_0 == 141.7001
    
    def test_phi_golden_ratio(self):
        """Test that φ is the golden ratio."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
    
    def test_c_threshold_value(self):
        """Test that C_threshold = 1/κ_Π ≈ 0.388."""
        expected = 1.0 / KAPPA_PI
        assert abs(C_THRESHOLD - expected) < 1e-10
        assert abs(C_THRESHOLD - 0.388) < 0.01
    
    def test_trinity_geometric_origin(self):
        """Test geometric origin: κ_Π = φ × (π/e) × λ_CY."""
        geometric = PHI * (math.pi / math.e) * LAMBDA_CY
        assert abs(geometric - KAPPA_PI) < 0.01
    
    def test_constants_container(self):
        """Test UniversalConstants container."""
        constants = UniversalConstants()
        assert constants.kappa_pi == KAPPA_PI
        assert constants.f_0 == F_0
        assert constants.phi == PHI
    
    def test_trinity_verification(self):
        """Test trinity verification method."""
        constants = UniversalConstants()
        trinity = constants.verify_trinity()
        
        assert 'kappa_pi' in trinity
        assert 'geometric_origin' in trinity
        assert 'physical_origin' in trinity
        assert trinity['geometric_match'] == True


class TestConsciousnessState:
    """Tests for consciousness state and quantization."""
    
    def test_consciousness_equation(self):
        """Test C = m × c² × A_eff²."""
        mass = 1e-9  # 1 nanogram
        coherence = 0.8
        
        state = ConsciousnessState(mass=mass, coherence=coherence)
        
        expected = mass * (SPEED_OF_LIGHT ** 2) * (coherence ** 2)
        assert abs(state.consciousness_level - expected) < 1e-10
    
    def test_relative_consciousness(self):
        """Test relative consciousness = A_eff²."""
        coherence = 0.7
        state = ConsciousnessState(mass=1e-9, coherence=coherence)
        
        assert abs(state.relative_consciousness - coherence ** 2) < 1e-10
    
    def test_threshold_classification_below(self):
        """Test classification for coherence below threshold."""
        # √C_threshold ≈ √0.388 ≈ 0.623
        low_coherence = 0.5  # Below √C_threshold
        state = ConsciousnessState(mass=1e-9, coherence=low_coherence)
        
        assert not state.is_above_threshold()
        assert state.complexity_class == ComplexityClass.POLYNOMIAL
    
    def test_threshold_classification_above(self):
        """Test classification for coherence above threshold."""
        # √C_threshold ≈ 0.623, so 0.7² = 0.49 > 0.388
        high_coherence = 0.7  # Above √C_threshold
        state = ConsciousnessState(mass=1e-9, coherence=high_coherence)
        
        assert state.is_above_threshold()
        assert state.complexity_class == ComplexityClass.EXPONENTIAL
    
    def test_exact_threshold(self):
        """Test exact threshold behavior."""
        # A_eff such that A_eff² = C_threshold
        exact_coherence = math.sqrt(C_THRESHOLD)
        state = ConsciousnessState(mass=1e-9, coherence=exact_coherence)
        
        # At exactly threshold, should be at or above
        assert state.relative_consciousness >= C_THRESHOLD - 1e-10
    
    def test_consciousness_analysis(self):
        """Test get_analysis method."""
        state = ConsciousnessState(mass=1e-9, coherence=0.8)
        analysis = state.get_analysis()
        
        assert 'mass_kg' in analysis
        assert 'coherence_A_eff' in analysis
        assert 'consciousness_C' in analysis
        assert 'complexity_class' in analysis
        assert 'threshold' in analysis
        assert analysis['kappa_pi'] == KAPPA_PI


class TestFrequencyAnalysis:
    """Tests for frequency-dependent complexity analysis."""
    
    def test_classical_frequency(self):
        """Test classical regime at ω = 0."""
        analysis = FrequencyAnalysis(omega=0.0, problem_size=100, treewidth=50)
        
        assert analysis.spectrum_state == SpectrumState.COLLAPSED
        assert abs(analysis.kappa_at_omega - KAPPA_PI) < 0.01
    
    def test_critical_frequency(self):
        """Test critical regime at ω = f₀."""
        analysis = FrequencyAnalysis(omega=F_0, problem_size=100, treewidth=50)
        
        assert analysis.spectrum_state == SpectrumState.REVEALED
        # κ_Π should decay at critical frequency
        assert analysis.kappa_at_omega < KAPPA_PI
    
    def test_kappa_decay_at_critical(self):
        """Test that κ_Π decays as O(1/(√n·log n)) at critical frequency."""
        n = 100
        analysis = FrequencyAnalysis(omega=F_0, problem_size=n, treewidth=50)
        
        # Expected decay factor
        sqrt_n = math.sqrt(n)
        log_n = math.log2(n)
        expected_kappa = KAPPA_PI / (sqrt_n * log_n)
        
        assert abs(analysis.kappa_at_omega - expected_kappa) < 0.01
    
    def test_ic_amplification(self):
        """Test IC amplification at critical frequency."""
        n = 100
        tw = 50
        
        classical = FrequencyAnalysis(omega=0.0, problem_size=n, treewidth=tw)
        critical = FrequencyAnalysis(omega=F_0, problem_size=n, treewidth=tw)
        
        # IC should be higher at critical frequency
        assert critical.ic > classical.ic
        
        # Amplification should be significant
        amplification = critical.ic / classical.ic
        assert amplification > 10  # Expect significant amplification
    
    def test_intermediate_frequency(self):
        """Test intermediate frequency regime."""
        analysis = FrequencyAnalysis(omega=50.0, problem_size=100, treewidth=50)
        
        assert analysis.spectrum_state == SpectrumState.PARTIAL
        # κ should be between classical and critical values
        classical_kappa = KAPPA_PI
        critical_analysis = FrequencyAnalysis(omega=F_0, problem_size=100, treewidth=50)
        
        assert analysis.kappa_at_omega <= classical_kappa
    
    def test_small_problem_size(self):
        """Test behavior for small problem sizes."""
        analysis = FrequencyAnalysis(omega=0.0, problem_size=1, treewidth=0)
        
        # Should handle gracefully
        assert analysis.kappa_at_omega == KAPPA_PI
        assert analysis.ic == 0.0
    
    def test_analysis_output(self):
        """Test get_analysis method."""
        analysis = FrequencyAnalysis(omega=F_0, problem_size=100, treewidth=50)
        result = analysis.get_analysis()
        
        assert 'frequency_omega' in result
        assert 'kappa_at_omega' in result
        assert 'information_complexity' in result
        assert 'spectrum_state' in result
        assert result['f_0'] == F_0


class TestPNPConsciousnessEquivalence:
    """Tests for P≠NP ↔ Consciousness Quantization equivalence."""
    
    def test_high_consciousness_implies_exponential(self):
        """Test that high consciousness implies exponential complexity."""
        state = ConsciousnessState(mass=1e-9, coherence=0.9)
        verification = verify_pnp_consciousness_equivalence(state)
        
        assert verification['is_above_threshold']
        assert verification['implied_complexity'] == 'EXPONENTIAL'
    
    def test_low_consciousness_implies_polynomial(self):
        """Test that low consciousness implies polynomial complexity."""
        state = ConsciousnessState(mass=1e-9, coherence=0.3)
        verification = verify_pnp_consciousness_equivalence(state)
        
        assert not verification['is_above_threshold']
        assert verification['implied_complexity'] == 'POLYNOMIAL'
    
    def test_verification_structure(self):
        """Test structure of verification result."""
        state = ConsciousnessState(mass=1e-9, coherence=0.7)
        verification = verify_pnp_consciousness_equivalence(state)
        
        assert 'consciousness_level' in verification
        assert 'threshold' in verification
        assert 'theorem_verification' in verification
        assert 'physical_constants' in verification
        
        assert verification['physical_constants']['kappa_pi'] == KAPPA_PI
        assert verification['physical_constants']['f_0'] == F_0


class TestFrequencyComparison:
    """Tests for frequency comparison analysis."""
    
    def test_comparison_structure(self):
        """Test structure of comparison result."""
        comparison = compare_frequencies(n=100, tw=50)
        
        assert 'classical' in comparison
        assert 'critical' in comparison
        assert 'amplification' in comparison
        assert 'insight' in comparison
    
    def test_kappa_decay_ratio(self):
        """Test κ_Π decay ratio between regimes."""
        comparison = compare_frequencies(n=100, tw=50)
        
        kappa_ratio = comparison['amplification']['kappa_decay']
        
        # Should be significant decay (> 10x)
        assert kappa_ratio > 10
    
    def test_ic_amplification_ratio(self):
        """Test IC amplification between regimes."""
        comparison = compare_frequencies(n=100, tw=50)
        
        ic_ratio = comparison['amplification']['IC_amplification']
        
        # Should match kappa decay (IC inversely proportional to κ_Π)
        assert ic_ratio > 10
    
    def test_spectrum_states(self):
        """Test spectrum states in comparison."""
        comparison = compare_frequencies(n=100, tw=50)
        
        assert comparison['classical']['spectrum'] == 'COLLAPSED'
        assert comparison['critical']['spectrum'] == 'REVEALED'


class TestUnificationAnalysis:
    """Tests for complete unification analysis."""
    
    def test_unification_thesis(self):
        """Test unification thesis is present."""
        unification = analyze_unification()
        
        assert 'thesis' in unification
        assert 'P≠NP' in unification['thesis']
        assert 'Cognition' in unification['thesis']
    
    def test_four_domains(self):
        """Test four domains are present."""
        unification = analyze_unification()
        
        domains = unification['domains']
        assert 'mathematics' in domains
        assert 'complexity' in domains
        assert 'physics' in domains
        assert 'consciousness' in domains
    
    def test_equivalence_chain(self):
        """Test equivalence chain is complete."""
        unification = analyze_unification()
        
        chain = unification['equivalence_chain']
        assert len(chain) >= 5  # At least 5 steps
        assert 'P ≠ NP' in chain[0]
        assert 'Cognition' in chain[-1] or 'physical' in chain[-1]
    
    def test_constants_included(self):
        """Test universal constants are included."""
        unification = analyze_unification()
        
        constants = unification['universal_constants']
        assert constants['kappa_pi'] == KAPPA_PI
        assert constants['f_0'] == F_0
        assert constants['phi'] == PHI


class TestIntegration:
    """Integration tests for the complete framework."""
    
    def test_consciousness_to_frequency_connection(self):
        """Test connection between consciousness and frequency analysis."""
        # High coherence consciousness
        high_state = ConsciousnessState(mass=1e-9, coherence=0.9)
        
        # Frequency analysis shows complexity
        n = 100
        tw = 50
        freq_analysis = FrequencyAnalysis(omega=F_0, problem_size=n, treewidth=tw)
        
        # Both should indicate exponential complexity
        assert high_state.complexity_class == ComplexityClass.EXPONENTIAL
        assert freq_analysis.ic > 100  # High IC at critical frequency
    
    def test_trinity_and_threshold_consistency(self):
        """Test consistency between trinity verification and threshold."""
        constants = UniversalConstants()
        trinity = constants.verify_trinity()
        
        # κ_Π from trinity should match C_threshold calculation
        kappa = trinity['kappa_pi']
        expected_threshold = 1.0 / kappa
        
        assert abs(C_THRESHOLD - expected_threshold) < 1e-10
    
    def test_frequency_independence_at_classical(self):
        """Test that κ_Π is constant at classical frequency regardless of n."""
        sizes = [10, 100, 1000]
        
        for n in sizes:
            analysis = FrequencyAnalysis(omega=0.0, problem_size=n, treewidth=n//2)
            assert abs(analysis.kappa_at_omega - KAPPA_PI) < 0.01
    
    def test_frequency_decay_scales_with_n(self):
        """Test that κ_Π decay at critical frequency scales with problem size."""
        analysis_small = FrequencyAnalysis(omega=F_0, problem_size=10, treewidth=5)
        analysis_large = FrequencyAnalysis(omega=F_0, problem_size=100, treewidth=50)
        
        # Larger problems should have smaller κ at critical frequency
        assert analysis_large.kappa_at_omega < analysis_small.kappa_at_omega


class TestEdgeCases:
    """Edge case tests."""
    
    def test_zero_coherence(self):
        """Test with zero coherence."""
        state = ConsciousnessState(mass=1e-9, coherence=0.0)
        
        assert state.consciousness_level == 0.0
        assert state.relative_consciousness == 0.0
        assert state.complexity_class == ComplexityClass.POLYNOMIAL
    
    def test_max_coherence(self):
        """Test with maximum coherence."""
        state = ConsciousnessState(mass=1e-9, coherence=A_EFF_MAX)
        
        assert state.is_above_threshold()
        assert state.complexity_class == ComplexityClass.EXPONENTIAL
    
    def test_zero_treewidth(self):
        """Test with zero treewidth."""
        analysis = FrequencyAnalysis(omega=F_0, problem_size=100, treewidth=0)
        
        assert analysis.ic == 0.0
    
    def test_problem_size_one(self):
        """Test with problem size of 1."""
        analysis = FrequencyAnalysis(omega=F_0, problem_size=1, treewidth=0)
        
        assert analysis.ic == 0.0
        assert analysis.kappa_at_omega == KAPPA_PI


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
