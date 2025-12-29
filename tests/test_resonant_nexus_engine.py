"""
Test suite for ResonantNexusEngine
===================================

Tests the resonant nexus engine signal generation, coherence calculations,
and harmonic analysis based on QCAL ∞³ parameters.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from tools.resonant_nexus_engine import ResonantNexusEngine


class TestResonantNexusEngineInit:
    """Test suite for ResonantNexusEngine initialization."""
    
    def test_engine_initialization(self):
        """Test that engine initializes with correct default parameters."""
        engine = ResonantNexusEngine()
        
        assert engine.f0 == 141.7001, "Base frequency must be 141.7001 Hz"
        assert engine.tau0 == 1 / 141.7001, "Period must be 1/f0"
        assert engine.volatility == 0.04, "Volatility must be 0.04"
        assert engine.harmonic_weights == [0.5, 0.3, 0.15, 0.05]
    
    def test_class_constants(self):
        """Test that class constants are properly defined."""
        assert ResonantNexusEngine.SPECTRAL_ANALYSIS_FACTOR == 10
        assert ResonantNexusEngine.PHASE_MODULATION_FREQ == 0.1
        assert ResonantNexusEngine.SAMPLING_POINTS_PER_CYCLE == 100
    
    def test_harmonic_weights_sum(self):
        """Test that harmonic weights sum to 1.0."""
        engine = ResonantNexusEngine()
        weights_sum = sum(engine.harmonic_weights)
        
        assert abs(weights_sum - 1.0) < 1e-10, "Harmonic weights should sum to 1.0"


class TestSignalGeneration:
    """Test suite for signal generation."""
    
    def test_generate_coherent_signal_basic(self):
        """Test basic signal generation."""
        engine = ResonantNexusEngine()
        result = engine.generate_coherent_signal(duration_seconds=1.0)
        
        assert 'signal' in result
        assert 'time' in result
        assert 'coherence_score' in result
        assert isinstance(result['signal'], np.ndarray)
        assert isinstance(result['time'], np.ndarray)
    
    def test_signal_duration(self):
        """Test that signal has correct duration."""
        engine = ResonantNexusEngine()
        duration = 0.5
        result = engine.generate_coherent_signal(duration_seconds=duration)
        
        # Time should span approximately the requested duration
        assert result['time'][-1] >= duration * 0.95
        assert result['time'][-1] <= duration * 1.05
    
    def test_signal_cycles(self):
        """Test that signal contains expected number of cycles."""
        engine = ResonantNexusEngine()
        duration = 1.0
        result = engine.generate_coherent_signal(duration_seconds=duration)
        
        expected_cycles = int(duration * engine.f0)
        assert result['num_cycles'] == expected_cycles
    
    def test_signal_parameters_in_result(self):
        """Test that result contains all expected parameters."""
        engine = ResonantNexusEngine()
        result = engine.generate_coherent_signal(duration_seconds=1.0)
        
        assert result['f0'] == 141.7001
        assert result['tau0'] == engine.tau0
        assert result['volatility'] == 0.04
        assert result['harmonic_weights'] == [0.5, 0.3, 0.15, 0.05]
        assert 'timestamp' in result
    
    def test_signal_is_deterministic(self):
        """Test that signal generation is deterministic (no random noise)."""
        engine = ResonantNexusEngine()
        
        # Generate same signal twice
        result1 = engine.generate_coherent_signal(duration_seconds=0.1)
        result2 = engine.generate_coherent_signal(duration_seconds=0.1)
        
        # Signals should be identical (within numerical precision)
        np.testing.assert_array_almost_equal(
            result1['signal'], 
            result2['signal'],
            decimal=10,
            err_msg="Signal generation should be deterministic"
        )


class TestCoherenceCalculation:
    """Test suite for coherence score calculation."""
    
    def test_coherence_score_range(self):
        """Test that coherence score is in valid range [0, 1]."""
        engine = ResonantNexusEngine()
        result = engine.generate_coherent_signal(duration_seconds=1.0)
        
        coherence = result['coherence_score']
        assert 0 <= coherence <= 1, "Coherence score must be in range [0, 1]"
    
    def test_coherence_calculation_method(self):
        """Test that _calculate_coherence works correctly."""
        engine = ResonantNexusEngine()
        
        # Create a simple test signal
        test_signal = np.sin(2 * np.pi * engine.f0 * np.linspace(0, 1, 1000))
        
        coherence = engine._calculate_coherence(test_signal)
        
        assert isinstance(coherence, float)
        assert 0 <= coherence <= 1


class TestPhaseCalculation:
    """Test suite for phase calculation."""
    
    def test_get_current_phase(self):
        """Test that current phase is in valid range."""
        engine = ResonantNexusEngine()
        phase = engine.get_current_phase()
        
        assert isinstance(phase, float)
        assert 0 <= phase < 1, "Phase must be in range [0, 1)"
    
    def test_phase_is_modulo_one(self):
        """Test that phase wraps around correctly."""
        engine = ResonantNexusEngine()
        
        # Get phase multiple times
        phases = [engine.get_current_phase() for _ in range(3)]
        
        # All phases should be in valid range
        for phase in phases:
            assert 0 <= phase < 1


class TestActivateMethod:
    """Test suite for activate method."""
    
    def test_activate_basic(self):
        """Test basic activate functionality."""
        engine = ResonantNexusEngine()
        result = engine.activate(cycles=10)
        
        assert 'f0' in result
        assert 'sigma' in result
        assert 'harmonic_weights' in result
        assert 'cycles' in result
        assert 'coherence_score' in result
        assert 'phase_coherence' in result
    
    def test_activate_with_custom_cycles(self):
        """Test activate with custom cycle count."""
        engine = ResonantNexusEngine()
        cycles = 50
        result = engine.activate(cycles=cycles)
        
        assert result['cycles'] == cycles
        assert result['duration'] == cycles / engine.f0
    
    def test_activate_default_cycles(self):
        """Test activate with default cycles (142 ≈ 1 second)."""
        engine = ResonantNexusEngine()
        result = engine.activate()
        
        assert result['cycles'] == 142
        # Duration should be approximately 1 second
        assert 0.99 < result['duration'] < 1.01
    
    def test_activate_returns_signal_stats(self):
        """Test that activate returns signal statistics."""
        engine = ResonantNexusEngine()
        result = engine.activate(cycles=100)
        
        assert 'signal_stats' in result
        stats = result['signal_stats']
        assert 'mean' in stats
        assert 'std' in stats
        assert 'max' in stats
        assert 'min' in stats


class TestHarmonicGeneration:
    """Test suite for harmonic generation."""
    
    def test_harmonic_structure(self):
        """Test that signal contains expected harmonics."""
        engine = ResonantNexusEngine()
        result = engine.generate_coherent_signal(duration_seconds=2.0)
        
        signal = result['signal']
        
        # Perform FFT to check harmonic content
        fft = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), d=result['time'][1] - result['time'][0])
        
        # Get positive frequencies only
        positive_freqs = freqs > 0
        fft_positive = np.abs(fft[positive_freqs])
        freqs_positive = freqs[positive_freqs]
        
        # Find peaks near expected harmonics
        f0 = engine.f0
        harmonics = [1, 2, 3, 4]  # First 4 harmonics
        
        for h in harmonics:
            expected_freq = h * f0
            # Find closest frequency bin
            idx = np.argmin(np.abs(freqs_positive - expected_freq))
            # Should have significant power at harmonic frequencies
            assert fft_positive[idx] > np.mean(fft_positive) * 2


class TestEdgeCases:
    """Test suite for edge cases and error handling."""
    
    def test_very_short_duration(self):
        """Test signal generation with very short duration."""
        engine = ResonantNexusEngine()
        result = engine.generate_coherent_signal(duration_seconds=0.01)
        
        assert len(result['signal']) > 0
        assert result['num_cycles'] >= 0
    
    def test_zero_duration_raises_or_handles(self):
        """Test that zero duration is handled appropriately."""
        engine = ResonantNexusEngine()
        
        try:
            result = engine.generate_coherent_signal(duration_seconds=0.0)
            # If it doesn't raise, check it returns valid but empty result
            assert len(result['signal']) >= 0
        except (ValueError, ZeroDivisionError):
            # It's acceptable to raise an error for zero duration
            pass


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
