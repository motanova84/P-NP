"""
Test Suite for Superfluid Coherence Module
===========================================

Comprehensive tests for P=NP resolution via superfluid coherence.

Tests:
- Coherence calculation
- Regime detection (NP Chaos, Transition, P Superfluid)
- Complexity collapse analysis
- Phase transitions
- Viscosity calculations

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from superfluid_coherence import (
    SuperfluidCoherence,
    ComplexityRegime,
    demonstrate_superfluid_transition
)


class TestSuperfluidCoherenceInitialization:
    """Test initialization of SuperfluidCoherence."""
    
    def test_default_initialization(self):
        """Test default initialization parameters."""
        sc = SuperfluidCoherence()
        
        assert sc.f0 == 141.7001
        assert sc.tau0 == pytest.approx(1.0 / 141.7001)
        assert sc.psi_chaos_threshold == 0.88
        assert sc.psi_superfluid_threshold == 0.99
        assert sc.kappa_pi == pytest.approx(2.5773302292)
    
    def test_custom_frequency(self):
        """Test initialization with custom frequency."""
        f0 = 100.0
        sc = SuperfluidCoherence(f0=f0)
        
        assert sc.f0 == f0
        assert sc.tau0 == pytest.approx(1.0 / f0)


class TestCoherenceCalculation:
    """Test coherence parameter calculation."""
    
    def test_zero_energy_zero_noise(self):
        """Test coherence with zero energy and zero noise."""
        sc = SuperfluidCoherence()
        psi = sc.calculate_coherence(energy=0.0, temperature=1.0, noise_level=0.0)
        
        # Should be maximum coherence
        assert psi > 0.9
        assert psi <= 1.0
    
    def test_high_energy_low_coherence(self):
        """Test that high energy leads to low coherence."""
        sc = SuperfluidCoherence()
        psi = sc.calculate_coherence(energy=10.0, temperature=1.0, noise_level=0.0)
        
        # High energy should reduce coherence
        assert psi < 0.5
    
    def test_high_noise_low_coherence(self):
        """Test that high noise reduces coherence."""
        sc = SuperfluidCoherence()
        psi = sc.calculate_coherence(energy=0.0, temperature=1.0, noise_level=0.9)
        
        # High noise should reduce coherence
        assert psi < 0.5
    
    def test_coherence_bounds(self):
        """Test that coherence is always in [0, 1]."""
        sc = SuperfluidCoherence()
        
        # Test various extreme cases
        test_cases = [
            (0.0, 1.0, 0.0),
            (100.0, 1.0, 0.0),
            (0.0, 1.0, 1.0),
            (10.0, 0.1, 0.5)
        ]
        
        for energy, temp, noise in test_cases:
            psi = sc.calculate_coherence(energy, temp, noise)
            assert 0.0 <= psi <= 1.0


class TestRegimeDetection:
    """Test complexity regime detection."""
    
    def test_np_chaos_regime(self):
        """Test detection of NP chaos regime (Ψ < 0.88)."""
        sc = SuperfluidCoherence()
        
        regime = sc.detect_regime(0.5)
        assert regime == ComplexityRegime.NP_CHAOS
        
        regime = sc.detect_regime(0.87)
        assert regime == ComplexityRegime.NP_CHAOS
    
    def test_transition_regime(self):
        """Test detection of transition regime (0.88 ≤ Ψ < 0.99)."""
        sc = SuperfluidCoherence()
        
        regime = sc.detect_regime(0.88)
        assert regime == ComplexityRegime.TRANSITION
        
        regime = sc.detect_regime(0.95)
        assert regime == ComplexityRegime.TRANSITION
        
        regime = sc.detect_regime(0.98)
        assert regime == ComplexityRegime.TRANSITION
    
    def test_p_superfluid_regime(self):
        """Test detection of P superfluid regime (Ψ ≥ 0.99)."""
        sc = SuperfluidCoherence()
        
        regime = sc.detect_regime(0.99)
        assert regime == ComplexityRegime.P_SUPERFLUID
        
        regime = sc.detect_regime(1.0)
        assert regime == ComplexityRegime.P_SUPERFLUID


class TestComplexityCollapseAnalysis:
    """Test complexity collapse detection and analysis."""
    
    def test_all_chaos_regime(self):
        """Test analysis when all states are in NP chaos."""
        sc = SuperfluidCoherence()
        
        # High energy, high noise -> chaos
        energies = [10.0, 8.0, 9.0]
        temps = [1.0, 1.0, 1.0]
        noise = [0.5, 0.5, 0.5]
        
        analysis = sc.analyze_complexity_collapse(energies, temps, noise)
        
        assert analysis['collapse_detected'] == False
        assert analysis['p_superfluid_count'] == 0
        assert analysis['np_chaos_count'] > 0
    
    def test_transition_to_superfluid(self):
        """Test transition from chaos to superfluid."""
        sc = SuperfluidCoherence()
        
        # Gradually decrease energy and noise
        energies = [5.0, 2.0, 0.5, 0.1, 0.01]
        temps = [1.0, 1.0, 1.0, 1.0, 1.0]
        noise = [0.5, 0.2, 0.1, 0.05, 0.001]
        
        analysis = sc.analyze_complexity_collapse(energies, temps, noise)
        
        # Should detect collapse
        assert analysis['collapse_detected'] == True
        assert analysis['p_superfluid_count'] > 0
        assert len(analysis['superfluid_indices']) > 0
    
    def test_collapse_fraction(self):
        """Test collapse fraction calculation."""
        sc = SuperfluidCoherence()
        
        # Mix of regimes
        energies = [10.0, 5.0, 1.0, 0.1, 0.01]
        temps = [1.0] * 5
        noise = [0.5, 0.3, 0.1, 0.05, 0.001]
        
        analysis = sc.analyze_complexity_collapse(energies, temps, noise)
        
        assert 0.0 <= analysis['collapse_fraction'] <= 1.0
        assert analysis['mean_coherence'] > 0.0


class TestSuperfluidFraction:
    """Test superfluid fraction calculation."""
    
    def test_zero_below_threshold(self):
        """Test that superfluid fraction is zero below Ψ_c."""
        sc = SuperfluidCoherence()
        
        f_s = sc.calculate_superfluid_fraction(psi=0.5, temperature=1.0)
        assert f_s == 0.0
        
        f_s = sc.calculate_superfluid_fraction(psi=0.87, temperature=1.0)
        assert f_s == 0.0
    
    def test_nonzero_above_threshold(self):
        """Test that superfluid fraction is nonzero above Ψ_c."""
        sc = SuperfluidCoherence()
        
        f_s = sc.calculate_superfluid_fraction(psi=0.90, temperature=1.0)
        assert f_s > 0.0
        
        f_s = sc.calculate_superfluid_fraction(psi=0.99, temperature=1.0)
        assert f_s > 0.0
    
    def test_increases_with_coherence(self):
        """Test that f_s increases with Ψ."""
        sc = SuperfluidCoherence()
        
        f_s_90 = sc.calculate_superfluid_fraction(psi=0.90, temperature=1.0)
        f_s_95 = sc.calculate_superfluid_fraction(psi=0.95, temperature=1.0)
        f_s_99 = sc.calculate_superfluid_fraction(psi=0.99, temperature=1.0)
        
        assert f_s_90 < f_s_95 < f_s_99


class TestPhaseTransitionDetection:
    """Test phase transition detection."""
    
    def test_no_transition(self):
        """Test when no phase transition occurs."""
        sc = SuperfluidCoherence()
        
        # All in same regime
        coherences = [0.5, 0.6, 0.7, 0.75]
        
        result = sc.detect_phase_transition(coherences)
        
        assert result['transition_count'] == 0
        assert result['critical_count'] == 0
        assert result['has_collapse'] == False
    
    def test_single_transition(self):
        """Test detection of single phase transition."""
        sc = SuperfluidCoherence()
        
        # Transition from chaos to transition regime
        coherences = [0.5, 0.7, 0.89, 0.92]
        
        result = sc.detect_phase_transition(coherences)
        
        assert result['transition_count'] > 0
    
    def test_critical_transition(self):
        """Test detection of critical NP -> P transition."""
        sc = SuperfluidCoherence()
        
        # Critical transition: chaos -> superfluid
        coherences = [0.5, 0.7, 0.85, 0.99]
        
        result = sc.detect_phase_transition(coherences)
        
        # Should detect critical transition
        assert result['has_collapse'] == True
        assert result['critical_count'] > 0


class TestViscosityCalculation:
    """Test viscosity calculation."""
    
    def test_high_viscosity_in_chaos(self):
        """Test high viscosity in NP chaos regime."""
        sc = SuperfluidCoherence()
        
        eta = sc.calculate_viscosity(psi=0.5, temperature=1.0)
        
        # Should have high viscosity
        assert eta > 0.8
    
    def test_low_viscosity_in_superfluid(self):
        """Test near-zero viscosity in P superfluid regime."""
        sc = SuperfluidCoherence()
        
        eta = sc.calculate_viscosity(psi=0.99, temperature=1.0)
        
        # Should have very low viscosity
        assert eta < 0.1
    
    def test_viscosity_decreases_with_coherence(self):
        """Test that viscosity decreases as coherence increases."""
        sc = SuperfluidCoherence()
        
        eta_50 = sc.calculate_viscosity(psi=0.5, temperature=1.0)
        eta_90 = sc.calculate_viscosity(psi=0.90, temperature=1.0)
        eta_99 = sc.calculate_viscosity(psi=0.99, temperature=1.0)
        
        assert eta_50 > eta_90 > eta_99


class TestReportGeneration:
    """Test coherence analysis report generation."""
    
    def test_report_generation(self):
        """Test that report is generated correctly."""
        sc = SuperfluidCoherence()
        
        energies = [5.0, 1.0, 0.1]
        temps = [1.0, 1.0, 1.0]
        noise = [0.5, 0.1, 0.001]
        
        analysis = sc.analyze_complexity_collapse(energies, temps, noise)
        report = sc.generate_coherence_report(analysis)
        
        assert isinstance(report, str)
        assert len(report) > 0
        assert "SUPERFLUID COHERENCE ANALYSIS REPORT" in report
        assert "Ψ" in report or "Psi" in report


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_transition_workflow(self):
        """Test complete transition from NP to P."""
        sc = SuperfluidCoherence(f0=141.7001)
        
        # Simulate cooling and noise reduction
        n_steps = 50
        energies = np.linspace(5.0, 0.01, n_steps).tolist()
        temps = np.linspace(2.0, 0.5, n_steps).tolist()
        noise = np.linspace(0.5, 0.001, n_steps).tolist()
        
        # Analyze
        analysis = sc.analyze_complexity_collapse(energies, temps, noise)
        
        # Should detect collapse
        assert analysis['collapse_detected'] == True
        
        # Should have mix of regimes
        assert analysis['np_chaos_count'] > 0
        assert analysis['p_superfluid_count'] > 0
        
        # Coherence should increase
        coherences = analysis['coherences']
        assert coherences[-1] > coherences[0]
    
    def test_demonstrate_function(self):
        """Test that demonstration function runs without error."""
        # Just ensure it doesn't crash
        try:
            # Redirect output to suppress prints
            import io
            import sys
            old_stdout = sys.stdout
            sys.stdout = io.StringIO()
            
            demonstrate_superfluid_transition()
            
            sys.stdout = old_stdout
            
            success = True
        except Exception as e:
            success = False
        
        assert success == True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
