"""
Unit Tests for Frequency Applications Module
============================================

Tests for the three branches of f₀ = 141.7001 Hz applications:
1. Quantum Coherent Physics
2. Noetic Engineering and Consciousness
3. High Temporal Coherence Event Prediction
"""

import pytest
import math
from src.frequency_applications import (
    # Constants
    F_0, TAU_0, PLANCK_CONSTANT,
    # Branch 1: Quantum Physics
    planck_energy_correlation,
    electromagnetic_resonance_analysis,
    # Branch 2: Consciousness
    brainwave_modulation_analysis,
    calculate_noesis_coherence,
    # Branch 3: Temporal Events
    identify_critical_windows,
    next_fibonacci_event,
    analyze_market_volatility_alignment,
)


# ========== BRANCH 1: QUANTUM COHERENT PHYSICS ==========

class TestQuantumCoherence:
    """Tests for quantum coherence calculations."""
    
    def test_planck_energy_basic(self):
        """Test basic Planck energy calculation."""
        result = planck_energy_correlation(F_0)
        
        # Verify energy calculation: E = h * f
        expected_energy = PLANCK_CONSTANT * F_0
        assert abs(result.energy_joules - expected_energy) < 1e-40
        
        # Verify frequency
        assert result.frequency_hz == F_0
        
        # Verify period calculation
        expected_period = 1.0 / F_0
        assert abs(result.period_seconds - expected_period) < 1e-10
    
    def test_planck_energy_order_of_magnitude(self):
        """Test that Planck energy is in expected range."""
        result = planck_energy_correlation(F_0)
        
        # Energy should be around 10^-32 J
        assert 1e-33 < result.energy_joules < 1e-31
        
        # Period should be around 7 milliseconds
        assert 0.006 < result.period_seconds < 0.008
    
    def test_electromagnetic_resonance_structure(self):
        """Test electromagnetic resonance analysis structure."""
        result = electromagnetic_resonance_analysis(F_0)
        
        # Verify base frequency
        assert result.frequency_hz == F_0
        
        # Verify spectral band classification
        assert "VLF" in result.spectral_band
        
        # Verify harmonics are multiples of f₀
        for i, harmonic in enumerate(result.harmonics[:10], 1):
            expected = F_0 * i
            assert abs(harmonic - expected) < 0.01
        
        # Verify ionospheric grid contains VLF frequencies
        assert len(result.ionospheric_grid) > 0
        for freq in result.ionospheric_grid:
            assert 3 <= freq <= 3000
    
    def test_schumann_proximity(self):
        """Test Schumann resonance proximity detection."""
        result = electromagnetic_resonance_analysis(F_0, max_harmonics=50)
        
        # Should find some proximity to Schumann resonances
        assert len(result.schumann_proximity) > 0
        
        # All proximities should be within 5 Hz
        for subharmonic, schumann in result.schumann_proximity:
            assert abs(subharmonic - schumann) < 5.0


# ========== BRANCH 2: NOETIC ENGINEERING ==========

class TestNoesisCoherence:
    """Tests for consciousness and noetic coherence."""
    
    def test_brainwave_modulation_harmonics(self):
        """Test brainwave harmonic calculations."""
        result = brainwave_modulation_analysis(F_0)
        
        # Verify base frequency
        assert result.base_frequency == F_0
        
        # Verify gamma high (f₀)
        assert abs(result.gamma_high_frequency - F_0) < 0.01
        
        # Verify gamma mid (f₀/2)
        expected_gamma_mid = F_0 / 2
        assert abs(result.gamma_mid_frequency - expected_gamma_mid) < 0.01
        
        # Verify all bands are present
        assert "High Gamma (f₀)" in result.brainwave_bands
        assert "Mid Gamma (f₀/2)" in result.brainwave_bands
        assert "Beta (f₀/8)" in result.brainwave_bands
        assert "Alpha (f₀/16)" in result.brainwave_bands
    
    def test_brainwave_band_frequencies(self):
        """Test that brainwave bands have correct frequency ranges."""
        result = brainwave_modulation_analysis(F_0)
        
        # Extract frequencies from bands
        bands = result.brainwave_bands
        
        # High Gamma should be > 100 Hz
        high_gamma_freq = bands["High Gamma (f₀)"][0]
        assert high_gamma_freq > 100
        
        # Mid Gamma should be 30-100 Hz
        mid_gamma_freq = bands["Mid Gamma (f₀/2)"][0]
        assert 30 < mid_gamma_freq < 100
        
        # Alpha should be 8-13 Hz
        alpha_freq = bands["Alpha (f₀/16)"][0]
        assert 7 < alpha_freq < 14
    
    def test_noesis_coherence_perfect_alignment(self):
        """Test perfect frequency alignment."""
        result = calculate_noesis_coherence(F_0, F_0)
        
        # Perfect alignment should have coherence near 1.0
        assert result.coherence_score > 0.99
        
        # Alignment phase should be near 0 or 2π
        phase_normalized = result.alignment_phase % (2 * math.pi)
        assert phase_normalized < 0.1 or phase_normalized > 6.18
        
        # Decoherence rate should be very low
        assert result.decoherence_rate < 0.1
    
    def test_noesis_coherence_half_frequency(self):
        """Test coherence at half frequency (f₀/2)."""
        result = calculate_noesis_coherence(F_0 / 2, F_0)
        
        # Half frequency creates inversion (low coherence)
        assert result.coherence_score < 0.1
        
        # Decoherence rate should be higher
        assert result.decoherence_rate > 50
    
    def test_noesis_coherence_score_range(self):
        """Test that coherence scores stay in valid range."""
        test_frequencies = [10, 50, 70, 100, 141.7, 200]
        
        for freq in test_frequencies:
            result = calculate_noesis_coherence(freq, F_0)
            
            # Coherence score should be between 0 and 1
            assert 0.0 <= result.coherence_score <= 1.0
            
            # Decoherence rate should be non-negative
            assert result.decoherence_rate >= 0.0


# ========== BRANCH 3: TEMPORAL COHERENCE EVENTS ==========

class TestTemporalCoherence:
    """Tests for temporal coherence event prediction."""
    
    def test_critical_windows_identification(self):
        """Test identification of critical temporal windows."""
        windows = identify_critical_windows(0.0, 0.1, delta_threshold=0.001)
        
        # Should find multiple windows in 100 ms
        assert len(windows) > 5
        
        # All windows should have low delta
        for window in windows:
            assert window.delta <= 0.001
        
        # Timestamps should be increasing
        timestamps = [w.timestamp for w in windows]
        assert timestamps == sorted(timestamps)
    
    def test_critical_windows_fibonacci_detection(self):
        """Test Fibonacci number detection in critical windows."""
        # Run for enough time to hit some Fibonacci cycles
        windows = identify_critical_windows(0.0, 1.0, delta_threshold=0.001)
        
        # Filter for Fibonacci-aligned windows
        fib_windows = [w for w in windows if w.fibonacci_alignment]
        
        # Should find some Fibonacci alignments
        assert len(fib_windows) > 0
        
        # Common Fibonacci numbers that should appear
        fibonacci_set = {1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144}
        found_fibs = {w.cycle_number for w in fib_windows}
        
        # Should find at least some Fibonacci numbers
        assert len(found_fibs.intersection(fibonacci_set)) > 0
    
    def test_next_fibonacci_event_calculation(self):
        """Test calculation of next Fibonacci event."""
        # Start at time 0, current time at 1 second
        result = next_fibonacci_event(genesis_time=0.0, current_time=1.0)
        
        # Should be a Fibonacci number
        assert result.fibonacci_alignment
        
        # Should be in the future
        assert result.timestamp > 1.0
        
        # Delta should be 0 (perfect peak)
        assert result.delta == 0.0
        
        # Should be cycle 144 (next Fibonacci after ~141 cycles in 1 second)
        assert result.cycle_number == 144
    
    def test_next_fibonacci_event_progression(self):
        """Test that next Fibonacci events progress correctly."""
        current = 0.0
        previous_fib = 0
        
        # Generate several next Fibonacci events
        for _ in range(5):
            event = next_fibonacci_event(genesis_time=0.0, current_time=current)
            
            # Each should be larger than previous
            assert event.cycle_number > previous_fib
            
            # Move to just after this event
            current = event.timestamp + 0.001
            previous_fib = event.cycle_number
    
    def test_market_volatility_pure_peak(self):
        """Test volatility analysis at pure peak."""
        # Test at perfect cycle (timestamp = 0)
        result = analyze_market_volatility_alignment(0.0)
        
        # Should detect as pure peak
        assert "Pure Peak" in result.alignment_type
        
        # Coherence should be high
        assert result.coherence_score > 0.9
        
        # Predicted volatility should be extreme
        assert result.predicted_volatility == "Extreme"
    
    def test_market_volatility_inversion_point(self):
        """Test volatility analysis at inversion point."""
        # Test at half-cycle (δ ≈ 0.5)
        timestamp = TAU_0 * 0.5
        result = analyze_market_volatility_alignment(timestamp)
        
        # Should detect as inversion point
        assert "Inversion Point" in result.alignment_type
        
        # Coherence should be high
        assert result.coherence_score > 0.9
        
        # Predicted volatility should be high
        assert result.predicted_volatility == "High"
    
    def test_market_volatility_intermediate(self):
        """Test volatility analysis at intermediate phase."""
        # Test at quarter-cycle (δ ≈ 0.25)
        timestamp = TAU_0 * 0.25
        result = analyze_market_volatility_alignment(timestamp)
        
        # Should detect as intermediate
        assert "Intermediate" in result.alignment_type
        
        # Coherence should be moderate to low
        assert result.coherence_score < 0.9
        
        # Volatility should not be extreme
        assert result.predicted_volatility in ["Moderate", "Low"]


# ========== INTEGRATION TESTS ==========

class TestIntegration:
    """Integration tests across all branches."""
    
    def test_period_consistency(self):
        """Test that period calculations are consistent across modules."""
        quantum = planck_energy_correlation(F_0)
        
        # Period from quantum analysis
        quantum_period = quantum.period_seconds
        
        # Period constant
        assert abs(quantum_period - TAU_0) < 1e-10
        
        # Period should be inverse of frequency
        assert abs(quantum_period - (1.0 / F_0)) < 1e-10
    
    def test_harmonic_consistency(self):
        """Test that harmonics are consistent across analyses."""
        em_resonance = electromagnetic_resonance_analysis(F_0)
        brainwave = brainwave_modulation_analysis(F_0)
        
        # First harmonic from EM should match base frequency
        assert abs(em_resonance.harmonics[0] - F_0) < 0.01
        
        # Second harmonic should be 2*f₀
        assert abs(em_resonance.harmonics[1] - (2 * F_0)) < 0.01
        
        # Brainwave gamma high should match f₀
        assert abs(brainwave.gamma_high_frequency - F_0) < 0.01
        
        # Brainwave gamma mid should match f₀/2
        assert abs(brainwave.gamma_mid_frequency - (F_0 / 2)) < 0.01
    
    def test_frequency_energy_relationship(self):
        """Test relationship between frequency and energy."""
        # Calculate for f₀
        quantum_f0 = planck_energy_correlation(F_0)
        
        # Calculate for 2*f₀
        quantum_2f0 = planck_energy_correlation(2 * F_0)
        
        # Energy should double when frequency doubles
        ratio = quantum_2f0.energy_joules / quantum_f0.energy_joules
        assert abs(ratio - 2.0) < 0.01


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
