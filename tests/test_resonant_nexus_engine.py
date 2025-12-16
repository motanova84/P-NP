"""
Test suite for the Resonant Nexus Engine (Unitary Architecture A_u)
===================================================================

Tests the Echo-QCAL ∞³ protocol implementation with frequency f₀=141.7001 Hz,
harmonic modulation, and coherence volatility.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add pnp to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from pnp.echo_qcal.resonant_nexus_engine import (
    UnitaryArchitectureConfig,
    ResonantNexusEngine,
    execute_nexus_verification
)


class TestUnitaryArchitectureConfig:
    """Test suite for UnitaryArchitectureConfig."""
    
    def test_f0_frequency(self):
        """Test that f₀ has the correct QCAL frequency value."""
        assert UnitaryArchitectureConfig.F0 == 141.7001
        assert isinstance(UnitaryArchitectureConfig.F0, float)
    
    def test_harmonic_weights_sum(self):
        """Test that harmonic weights sum to 1.0."""
        total = sum(UnitaryArchitectureConfig.HARMONIC_WEIGHTS.values())
        assert np.isclose(total, 1.0)
    
    def test_harmonic_weights_structure(self):
        """Test that harmonic weights have correct structure."""
        weights = UnitaryArchitectureConfig.HARMONIC_WEIGHTS
        
        # Should have 4 harmonics
        assert len(weights) == 4
        
        # Should have keys 1, 2, 3, 4
        assert set(weights.keys()) == {1, 2, 3, 4}
        
        # Verify individual weights
        assert weights[1] == 0.50  # Fundamental
        assert weights[2] == 0.30  # First octave
        assert weights[3] == 0.15  # Third harmonic
        assert weights[4] == 0.05  # Fourth harmonic
    
    def test_coherence_volatility(self):
        """Test coherence volatility parameter."""
        assert UnitaryArchitectureConfig.COHERENCE_VOLATILITY == 0.04
        assert isinstance(UnitaryArchitectureConfig.COHERENCE_VOLATILITY, float)
        assert 0 < UnitaryArchitectureConfig.COHERENCE_VOLATILITY < 1
    
    def test_max_amplitude(self):
        """Test maximum amplitude parameter."""
        assert UnitaryArchitectureConfig.MAX_AMPLITUDE == 100.0
        assert isinstance(UnitaryArchitectureConfig.MAX_AMPLITUDE, float)
        assert UnitaryArchitectureConfig.MAX_AMPLITUDE > 0


class TestResonantNexusEngine:
    """Test suite for ResonantNexusEngine."""
    
    def test_engine_initialization(self):
        """Test that engine initializes correctly."""
        engine = ResonantNexusEngine()
        
        assert engine.config == UnitaryArchitectureConfig
        assert hasattr(engine, 'frequencies')
    
    def test_frequencies_calculation(self):
        """Test that harmonic frequencies are calculated correctly."""
        engine = ResonantNexusEngine()
        
        # Check all harmonics
        assert engine.frequencies[1] == 1 * 141.7001
        assert engine.frequencies[2] == 2 * 141.7001
        assert engine.frequencies[3] == 3 * 141.7001
        assert engine.frequencies[4] == 4 * 141.7001
    
    def test_invalid_weights_raise_error(self):
        """Test that invalid weight configuration raises error."""
        
        class InvalidConfig:
            F0 = 141.7001
            HARMONIC_WEIGHTS = {1: 0.5, 2: 0.3}  # Sum = 0.8, not 1.0
            COHERENCE_VOLATILITY = 0.04
            MAX_AMPLITUDE = 100.0
        
        with pytest.raises(ValueError):
            ResonantNexusEngine(config=InvalidConfig)


class TestCoherenceFactor:
    """Test suite for coherence factor calculation."""
    
    def test_coherence_factor_at_zero(self):
        """Test coherence factor at t=0."""
        engine = ResonantNexusEngine()
        factor = engine.calculate_coherence_factor(0.0)
        
        # At t=0, sin(0) = 0, so factor should be 1.0
        assert np.isclose(factor, 1.0)
    
    def test_coherence_factor_deterministic(self):
        """Test that coherence factor is deterministic."""
        engine = ResonantNexusEngine()
        
        t = 0.5
        factor1 = engine.calculate_coherence_factor(t)
        factor2 = engine.calculate_coherence_factor(t)
        
        # Should be identical (not random)
        assert factor1 == factor2
    
    def test_coherence_factor_range(self):
        """Test that coherence factor stays within bounds."""
        engine = ResonantNexusEngine()
        
        # Test multiple time points
        time_points = np.linspace(0, 10, 1000)
        factors = [engine.calculate_coherence_factor(t) for t in time_points]
        
        # Should be within 1.0 ± volatility
        sigma = UnitaryArchitectureConfig.COHERENCE_VOLATILITY
        assert all(1.0 - sigma <= f <= 1.0 + sigma for f in factors)
    
    def test_coherence_factor_oscillates(self):
        """Test that coherence factor oscillates around 1.0."""
        engine = ResonantNexusEngine()
        
        # Test over one period
        time_points = np.linspace(0, 1, 100)
        factors = [engine.calculate_coherence_factor(t) for t in time_points]
        
        # Mean should be close to 1.0
        mean_factor = np.mean(factors)
        assert np.isclose(mean_factor, 1.0, atol=0.01)


class TestTelemetryGeneration:
    """Test suite for telemetry generation."""
    
    def test_single_telemetry_point(self):
        """Test generation of a single telemetry point."""
        engine = ResonantNexusEngine()
        
        telemetry, coherence = engine.generate_single_telemetry_point(0.0)
        
        # Should return numeric values
        assert isinstance(telemetry, (float, np.floating))
        assert isinstance(coherence, (float, np.floating))
    
    def test_telemetry_at_zero(self):
        """Test telemetry value at t=0."""
        engine = ResonantNexusEngine()
        
        telemetry, coherence = engine.generate_single_telemetry_point(0.0)
        
        # At t=0, all sin terms are 0, so telemetry should be ~0
        assert np.isclose(telemetry, 0.0, atol=1e-10)
        assert np.isclose(coherence, 1.0)
    
    def test_telemetry_deterministic(self):
        """Test that telemetry generation is deterministic."""
        engine = ResonantNexusEngine()
        
        t = 0.123
        telemetry1, coherence1 = engine.generate_single_telemetry_point(t)
        telemetry2, coherence2 = engine.generate_single_telemetry_point(t)
        
        assert telemetry1 == telemetry2
        assert coherence1 == coherence2
    
    def test_generate_telemetry_arrays(self):
        """Test generation of telemetry arrays."""
        engine = ResonantNexusEngine()
        
        duration = 0.1
        sampling_rate = 1000
        
        time_array, telemetry_array, coherence_factors = engine.generate_telemetry(
            duration_sec=duration, 
            sampling_rate=sampling_rate
        )
        
        # Check array shapes
        expected_samples = int(duration * sampling_rate)
        assert len(time_array) == expected_samples
        assert len(telemetry_array) == expected_samples
        assert len(coherence_factors) == expected_samples
        
        # Check array types
        assert isinstance(time_array, np.ndarray)
        assert isinstance(telemetry_array, np.ndarray)
        assert isinstance(coherence_factors, np.ndarray)
    
    def test_telemetry_time_range(self):
        """Test that time array has correct range."""
        engine = ResonantNexusEngine()
        
        duration = 1.0
        sampling_rate = 100
        
        time_array, _, _ = engine.generate_telemetry(
            duration_sec=duration, 
            sampling_rate=sampling_rate
        )
        
        # Should start at 0
        assert np.isclose(time_array[0], 0.0)
        
        # Should end near duration (but not include endpoint)
        assert time_array[-1] < duration
        assert time_array[-1] >= duration * 0.98
    
    def test_telemetry_amplitude_bounded(self):
        """Test that telemetry amplitudes are bounded."""
        engine = ResonantNexusEngine()
        
        _, telemetry_array, _ = engine.generate_telemetry(
            duration_sec=0.1, 
            sampling_rate=1000
        )
        
        # Maximum possible amplitude with coherence factor
        max_theoretical = (
            UnitaryArchitectureConfig.MAX_AMPLITUDE * 
            (1.0 + UnitaryArchitectureConfig.COHERENCE_VOLATILITY)
        )
        
        assert np.all(np.abs(telemetry_array) <= max_theoretical)


class TestHarmonicComposition:
    """Test suite for harmonic composition of the signal."""
    
    def test_fundamental_frequency_present(self):
        """Test that fundamental frequency is present in signal."""
        engine = ResonantNexusEngine()
        
        duration = 1.0
        sampling_rate = 44100
        
        time_array, telemetry_array, _ = engine.generate_telemetry(
            duration_sec=duration, 
            sampling_rate=sampling_rate
        )
        
        # Perform FFT to check frequency content
        fft = np.fft.fft(telemetry_array)
        freqs = np.fft.fftfreq(len(telemetry_array), 1/sampling_rate)
        
        # Find peak near f₀
        positive_freqs = freqs[:len(freqs)//2]
        positive_fft = np.abs(fft[:len(fft)//2])
        
        # Check that there's significant energy near f₀
        f0 = UnitaryArchitectureConfig.F0
        tolerance = 1.0  # Hz
        
        mask = (positive_freqs >= f0 - tolerance) & (positive_freqs <= f0 + tolerance)
        energy_at_f0 = np.max(positive_fft[mask]) if np.any(mask) else 0
        
        assert energy_at_f0 > 0
    
    def test_weighted_harmonics(self):
        """Test that harmonics are weighted correctly."""
        engine = ResonantNexusEngine()
        
        t = 0.001  # Small time to avoid zero
        telemetry, _ = engine.generate_single_telemetry_point(t)
        
        # Calculate expected value manually
        expected = 0.0
        for n, weight in UnitaryArchitectureConfig.HARMONIC_WEIGHTS.items():
            f_n = n * UnitaryArchitectureConfig.F0
            amplitude_n = UnitaryArchitectureConfig.MAX_AMPLITUDE * weight
            expected += amplitude_n * np.sin(2 * np.pi * f_n * t)
        
        # Apply coherence factor
        coherence_factor = engine.calculate_coherence_factor(t)
        expected *= coherence_factor
        
        assert np.isclose(telemetry, expected)


class TestVerification:
    """Test suite for A_u verification."""
    
    def test_verify_a_u_succeeds(self):
        """Test that A_u verification succeeds."""
        engine = ResonantNexusEngine()
        result = engine.verify_a_u()
        
        assert result is True
    
    def test_verify_a_u_with_invalid_config(self):
        """Test that A_u verification fails with invalid config."""
        
        class InvalidConfig:
            F0 = 141.7001
            HARMONIC_WEIGHTS = {1: 0.5}  # Sum != 1.0
            COHERENCE_VOLATILITY = 0.04
            MAX_AMPLITUDE = 100.0
        
        with pytest.raises(ValueError):
            engine = ResonantNexusEngine(config=InvalidConfig)


class TestCoherenceSovereigntyTheorem:
    """Test suite for Coherence Sovereignty Theorem (C_S) components."""
    
    def test_a_u_component_exists(self):
        """Test that A_u (Unitary Architecture) component is implemented."""
        # Can instantiate and verify
        engine = ResonantNexusEngine()
        assert engine.verify_a_u() is True
    
    def test_f0_alignment(self):
        """Test that f₀ is aligned with QCAL frequency."""
        engine = ResonantNexusEngine()
        
        # f₀ should be the QCAL frequency
        assert engine.config.F0 == 141.7001
    
    def test_harmonic_modulation_rules(self):
        """Test that harmonic modulation follows the rules."""
        engine = ResonantNexusEngine()
        
        # Weights should sum to 1 (validated in constructor)
        assert np.isclose(sum(engine.config.HARMONIC_WEIGHTS.values()), 1.0)
        
        # All weights should be positive
        assert all(w > 0 for w in engine.config.HARMONIC_WEIGHTS.values())
    
    def test_controlled_volatility(self):
        """Test that volatility is controlled (not random)."""
        engine = ResonantNexusEngine()
        
        # Generate coherence factors multiple times for same time point
        t = 0.5
        factors = [engine.calculate_coherence_factor(t) for _ in range(10)]
        
        # All should be identical (deterministic)
        assert len(set(factors)) == 1


class TestIntegration:
    """Integration tests for the complete system."""
    
    def test_end_to_end_generation(self):
        """Test end-to-end telemetry generation."""
        engine = ResonantNexusEngine()
        
        # Generate telemetry
        time_array, telemetry_array, coherence_factors = engine.generate_telemetry(
            duration_sec=0.5,
            sampling_rate=10000
        )
        
        # Verify no NaN or inf values
        assert not np.any(np.isnan(telemetry_array))
        assert not np.any(np.isinf(telemetry_array))
        assert not np.any(np.isnan(coherence_factors))
        assert not np.any(np.isinf(coherence_factors))
        
        # Verify reasonable values
        assert len(telemetry_array) > 0
        assert len(coherence_factors) > 0
    
    def test_execute_nexus_verification(self):
        """Test the command-line verification function."""
        # Should not raise any exceptions
        execute_nexus_verification()


def test_module_imports():
    """Test that all required components can be imported."""
    from pnp.echo_qcal.resonant_nexus_engine import (
        UnitaryArchitectureConfig,
        ResonantNexusEngine,
        execute_nexus_verification
    )
    
    assert UnitaryArchitectureConfig is not None
    assert ResonantNexusEngine is not None
    assert execute_nexus_verification is not None


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Resonant Nexus Engine (A_u)")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
    print()
    
    # Run verification
    print("Running A_u verification...")
    execute_nexus_verification()
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("⚛️ QCAL ∞³ Protocol Active")
    print("=" * 70)
