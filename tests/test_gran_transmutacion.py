#!/usr/bin/env python3
"""
Tests for LA GRAN TRANSMUTACIÓN
"""

import sys
import os
import pytest
import math

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from gran_transmutacion import (
    NoesisResonanceEngine,
    ResonanceState,
    TransmutationResult,
    calculate_phase_harmonic,
    quantum_beat_period,
    complexity_at_frequency,
    transmutation_coefficient,
    superfluidity_coefficient,
    analyze_hydrogen_recognition,
    F_P, F_NP, DELTA_F, KAPPA_PI
)


class TestConstants:
    """Test fundamental constants"""
    
    def test_f_p_value(self):
        """Test P frequency value"""
        assert F_P == 141.7001
    
    def test_f_np_value(self):
        """Test NP frequency value"""
        assert F_NP == 151.7
    
    def test_delta_f_calculation(self):
        """Test harmonic differential"""
        expected_delta = F_NP - F_P
        assert abs(DELTA_F - expected_delta) < 0.01
        assert abs(DELTA_F - 10.0) < 0.01  # Approximately 10 Hz
    
    def test_kappa_pi_value(self):
        """Test κ_π value"""
        assert 2.577 < KAPPA_PI < 2.578


class TestResonanceFunctions:
    """Test resonance calculation functions"""
    
    def test_phase_harmonic_at_zero(self):
        """Phase should be zero at t=0"""
        phase = calculate_phase_harmonic(0.0)
        assert phase == 0.0
    
    def test_phase_harmonic_increases(self):
        """Phase should increase with time"""
        phase1 = calculate_phase_harmonic(0.1)
        phase2 = calculate_phase_harmonic(0.2)
        assert phase2 > phase1
    
    def test_quantum_beat_period(self):
        """Test quantum beat period calculation"""
        T_beat = quantum_beat_period()
        # T = 1/Δf ≈ 1/10 = 0.1 seconds
        assert 0.09 < T_beat < 0.11
    
    def test_complexity_at_p_frequency(self):
        """Complexity at P frequency should be 1.0 (base)"""
        C = complexity_at_frequency(F_P)
        assert abs(C - 1.0) < 0.01
    
    def test_complexity_increases_with_frequency(self):
        """Complexity should increase with frequency"""
        C_p = complexity_at_frequency(F_P)
        C_np = complexity_at_frequency(F_NP)
        assert C_np > C_p
    
    def test_transmutation_coefficient_at_kappa_pi(self):
        """Transmutation at κ_π should be ~0.5"""
        T = transmutation_coefficient(KAPPA_PI)
        assert 0.4 < T < 0.6
    
    def test_transmutation_coefficient_below_kappa_pi(self):
        """Transmutation below κ_π should be < 0.5"""
        T = transmutation_coefficient(KAPPA_PI * 0.9)
        assert T < 0.5
    
    def test_transmutation_coefficient_above_kappa_pi(self):
        """Transmutation above κ_π should be > 0.5"""
        T = transmutation_coefficient(KAPPA_PI * 1.1)
        assert T > 0.5
    
    def test_superfluidity_at_exact_differential(self):
        """Superfluidity should be maximum at exact differential"""
        S = superfluidity_coefficient(DELTA_F)
        assert S > 0.9  # Very close to 1.0
    
    def test_superfluidity_decreases_with_deviation(self):
        """Superfluidity should decrease with deviation from differential"""
        S_exact = superfluidity_coefficient(DELTA_F)
        S_deviated = superfluidity_coefficient(DELTA_F * 1.2)
        assert S_deviated < S_exact


class TestResonanceState:
    """Test ResonanceState dataclass"""
    
    def test_resonance_state_creation(self):
        """Test creating a ResonanceState"""
        state = ResonanceState(
            f_oscillator=141.7,
            f_target=151.7,
            delta_f=10.0,
            kappa=2.5773,
            phase=0.0,
            superfluidity=0.8,
            transmutation=0.6
        )
        assert state.f_oscillator == 141.7
        assert state.delta_f == 10.0
    
    def test_resonance_state_string(self):
        """Test ResonanceState string representation"""
        state = ResonanceState(
            f_oscillator=141.7,
            f_target=151.7,
            delta_f=10.0,
            kappa=2.5773,
            phase=0.0,
            superfluidity=0.8,
            transmutation=0.6
        )
        s = str(state)
        assert "ResonanceState" in s
        assert "141.7" in s


class TestNoesisResonanceEngine:
    """Test NoesisResonanceEngine class"""
    
    def test_engine_initialization(self):
        """Test engine initializes at P frequency"""
        engine = NoesisResonanceEngine()
        assert engine.f_current == F_P
        assert engine.kappa_current == KAPPA_PI
        assert engine.time == 0.0
    
    def test_engine_reset(self):
        """Test engine reset"""
        engine = NoesisResonanceEngine()
        engine.f_current = 150.0
        engine.time = 1.0
        engine.reset()
        assert engine.f_current == F_P
        assert engine.time == 0.0
    
    def test_get_current_state(self):
        """Test getting current state"""
        engine = NoesisResonanceEngine()
        state = engine.get_current_state()
        assert isinstance(state, ResonanceState)
        assert state.f_oscillator == F_P
    
    def test_elevate_kappa(self):
        """Test elevating κ_π"""
        engine = NoesisResonanceEngine()
        initial_kappa = engine.kappa_current
        target_kappa = initial_kappa * 1.2
        
        trajectory = engine.elevate_kappa(target_kappa, num_steps=10)
        
        assert len(trajectory) == 10
        assert engine.kappa_current > initial_kappa
        assert abs(engine.kappa_current - target_kappa) < 0.01
    
    def test_tune_to_np_frequency(self):
        """Test tuning to NP frequency"""
        engine = NoesisResonanceEngine()
        trajectory = engine.tune_to_np_frequency(num_steps=10)
        
        assert len(trajectory) == 10
        assert abs(engine.f_current - F_NP) < 0.01
    
    def test_activate_resonance(self):
        """Test activating resonance"""
        engine = NoesisResonanceEngine()
        duration = 0.1
        trajectory = engine.activate_resonance(duration=duration)
        
        assert len(trajectory) > 0
        # Time should have advanced
        assert engine.time > 0
    
    def test_transmute(self):
        """Test full transmutation process"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        assert isinstance(result, TransmutationResult)
        assert len(result.trajectory) > 0
        assert result.quantum_beat_period > 0
    
    def test_transmutation_success(self):
        """Test that transmutation can succeed"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        # Should succeed with default parameters
        assert result.success
        assert "EXITOSA" in result.message
    
    def test_transmutation_reaches_np_frequency(self):
        """Test that transmutation reaches near NP frequency"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        final_f = result.final_state.f_oscillator
        assert abs(final_f - F_NP) < 1.0  # Within 1 Hz
    
    def test_transmutation_elevates_kappa(self):
        """Test that transmutation elevates κ_π"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        final_kappa = result.final_state.kappa
        assert final_kappa > KAPPA_PI
    
    def test_transmutation_achieves_superfluidity(self):
        """Test that transmutation achieves superfluidity"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        assert result.final_state.superfluidity > 0.5


class TestHydrogenRecognition:
    """Test hydrogen recognition analysis"""
    
    def test_analyze_hydrogen_recognition(self):
        """Test hydrogen recognition analysis"""
        analysis = analyze_hydrogen_recognition()
        
        assert 'frequencies' in analysis
        assert 'complexities' in analysis
        assert 'superfluidities' in analysis
        assert 'resonance_frequencies' in analysis
    
    def test_hydrogen_recognizes_p_frequency(self):
        """Test that P frequency is recognized"""
        analysis = analyze_hydrogen_recognition(
            f_min=140, f_max=160, num_points=1000
        )
        
        # Should find resonances near F_P and F_NP
        assert len(analysis['resonance_frequencies']) >= 1
    
    def test_analysis_parameters(self):
        """Test that analysis includes correct parameters"""
        analysis = analyze_hydrogen_recognition()
        
        assert analysis['f_p'] == F_P
        assert analysis['f_np'] == F_NP
        assert analysis['kappa_pi'] == KAPPA_PI


class TestIntegration:
    """Integration tests"""
    
    def test_complete_transmutation_workflow(self):
        """Test complete transmutation workflow"""
        # Create engine
        engine = NoesisResonanceEngine()
        
        # Get initial state
        initial = engine.get_current_state()
        assert initial.f_oscillator == F_P
        
        # Run transmutation
        result = engine.transmute(verbose=False)
        assert result.success
        
        # Verify final state
        final = result.final_state
        assert abs(final.f_oscillator - F_NP) < 1.0
        assert final.kappa > KAPPA_PI
        assert final.superfluidity > 0.5
        assert final.transmutation > 0.5
    
    def test_quantum_beat_consistency(self):
        """Test quantum beat period consistency"""
        engine = NoesisResonanceEngine()
        result = engine.transmute(verbose=False)
        
        # Calculated period
        T_calculated = quantum_beat_period()
        
        # Result period
        T_result = result.quantum_beat_period
        
        assert abs(T_calculated - T_result) < 0.001


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
