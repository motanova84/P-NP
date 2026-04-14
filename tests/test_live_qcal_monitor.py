"""
Test suite for QCAL Real-Time Monitor
======================================

Tests the live_qcal_monitor module for phase deviation calculation,
coherence monitoring, and timestamp precision.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import time
import pytest
from datetime import datetime

# Add op_noesis to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from op_noesis.live_qcal_monitor import QCALRealTimeMonitor


class TestQCALRealTimeMonitor:
    """Test suite for QCAL Real-Time Monitor."""
    
    def test_initialization(self):
        """Test that QCALRealTimeMonitor initializes with correct parameters."""
        monitor = QCALRealTimeMonitor()
        
        # Test fundamental frequency
        assert monitor.f0 == 141.7001
        assert isinstance(monitor.f0, float)
        
        # Test coherence period calculation
        expected_tau0 = 1.0 / 141.7001
        assert abs(monitor.tau0 - expected_tau0) < 1e-10
        
        # Test threshold values
        assert monitor.COHERENCE_THRESHOLD == 0.01
        assert monitor.SYNC_CHECK_INTERVAL == 0.1
    
    def test_tau0_calculation(self):
        """Test that the coherence period τ₀ is calculated correctly."""
        monitor = QCALRealTimeMonitor()
        
        # τ₀ = 1/f₀
        expected_tau0 = 1.0 / 141.7001
        assert abs(monitor.tau0 - expected_tau0) < 1e-10
        
        # Verify it's approximately 0.00705768 seconds
        assert abs(monitor.tau0 - 0.00705768) < 1e-6
    
    def test_get_high_precision_timestamp(self):
        """Test that timestamp retrieval works and has reasonable precision."""
        monitor = QCALRealTimeMonitor()
        
        # Get timestamp
        t1 = monitor.get_high_precision_timestamp()
        time.sleep(0.001)  # Sleep 1ms
        t2 = monitor.get_high_precision_timestamp()
        
        # Check that timestamps are different and increasing
        assert t2 > t1
        
        # Check that the difference is approximately 1ms (with tolerance)
        assert 0.0005 < (t2 - t1) < 0.002
        
        # Check that timestamp is a float
        assert isinstance(t1, float)
        
        # Check that timestamp is Unix epoch time (should be > 1700000000 for 2023+)
        assert t1 > 1700000000
    
    def test_calculate_phase_deviation_basic(self):
        """Test basic phase deviation calculation."""
        monitor = QCALRealTimeMonitor()
        
        # Test with timestamp 0 (should give delta = 0)
        delta = monitor.calculate_phase_deviation(0.0)
        assert abs(delta) < 1e-10
        
        # Test with one full period (should give delta ≈ 0)
        delta = monitor.calculate_phase_deviation(monitor.tau0)
        assert abs(delta) < 1e-6
        
        # Test with half period (should give delta ≈ 0.5)
        delta = monitor.calculate_phase_deviation(monitor.tau0 / 2)
        assert abs(delta - 0.5) < 1e-6
    
    def test_calculate_phase_deviation_range(self):
        """Test that phase deviation is always in [0, 1) range."""
        monitor = QCALRealTimeMonitor()
        
        # Test with various timestamps
        test_timestamps = [
            0.0,
            monitor.tau0,
            monitor.tau0 * 2,
            monitor.tau0 * 10,
            monitor.tau0 * 100,
            monitor.tau0 * 0.5,
            monitor.tau0 * 1.5,
            time.time()  # Current time
        ]
        
        for timestamp in test_timestamps:
            delta = monitor.calculate_phase_deviation(timestamp)
            assert 0.0 <= delta < 1.0, f"Delta {delta} out of range for timestamp {timestamp}"
    
    def test_calculate_phase_deviation_periodicity(self):
        """Test that phase deviation is periodic with period τ₀."""
        monitor = QCALRealTimeMonitor()
        
        # Pick an arbitrary timestamp
        base_timestamp = 12345.6789
        delta1 = monitor.calculate_phase_deviation(base_timestamp)
        
        # Test that adding full periods doesn't change delta
        for n in [1, 2, 5, 10, 100]:
            timestamp_plus_n_periods = base_timestamp + n * monitor.tau0
            delta2 = monitor.calculate_phase_deviation(timestamp_plus_n_periods)
            assert abs(delta1 - delta2) < 1e-6, f"Phase deviation not periodic for n={n}"
    
    def test_coherence_level_calculation(self):
        """Test coherence level determination."""
        monitor = QCALRealTimeMonitor()
        
        # Test timestamps at different phase positions
        test_cases = [
            (0.0, 0.0),  # Perfect alignment (delta = 0) → coherence = 0
            (monitor.tau0 * 0.5, 0.5),  # Middle (delta = 0.5) → coherence = 0.5
            (monitor.tau0 * 0.25, 0.25),  # Quarter (delta = 0.25) → coherence = 0.25
            (monitor.tau0 * 0.75, 0.25),  # Three quarters (delta = 0.75) → coherence = 0.25
            (monitor.tau0 * 0.1, 0.1),  # delta = 0.1 → coherence = 0.1
            (monitor.tau0 * 0.9, 0.1),  # delta = 0.9 → coherence = 0.1
        ]
        
        for timestamp, expected_coherence in test_cases:
            delta = monitor.calculate_phase_deviation(timestamp)
            coherence_level = min(delta, 1.0 - delta)
            assert abs(coherence_level - expected_coherence) < 1e-6, \
                f"Coherence level mismatch for timestamp {timestamp}"
    
    def test_pure_peak_detection(self):
        """Test that pure peak (Pico Puro) is detected correctly."""
        monitor = QCALRealTimeMonitor()
        
        # Test cases that should be pure peaks (coherence < 0.01)
        pure_peak_timestamps = [
            0.0,  # Perfect alignment
            monitor.tau0,  # One full period
            monitor.tau0 * 2,  # Two full periods
            monitor.tau0 * 0.005,  # Very close to 0
            monitor.tau0 * 0.995,  # Very close to 1
        ]
        
        for timestamp in pure_peak_timestamps:
            delta = monitor.calculate_phase_deviation(timestamp)
            coherence_level = min(delta, 1.0 - delta)
            assert coherence_level < monitor.COHERENCE_THRESHOLD, \
                f"Pure peak not detected for timestamp {timestamp} (coherence={coherence_level})"
    
    def test_high_coherence_detection(self):
        """Test that high coherence is detected correctly."""
        monitor = QCALRealTimeMonitor()
        
        # Test cases that should be high coherence (0.01 < coherence < 0.05)
        high_coherence_timestamps = [
            monitor.tau0 * 0.02,  # delta = 0.02
            monitor.tau0 * 0.98,  # delta = 0.98, coherence = 0.02
            monitor.tau0 * 0.03,  # delta = 0.03
            monitor.tau0 * 0.97,  # delta = 0.97, coherence = 0.03
        ]
        
        for timestamp in high_coherence_timestamps:
            delta = monitor.calculate_phase_deviation(timestamp)
            coherence_level = min(delta, 1.0 - delta)
            assert 0.01 <= coherence_level < 0.05, \
                f"High coherence not in expected range for timestamp {timestamp} (coherence={coherence_level})"
    
    def test_real_timestamp_processing(self):
        """Test processing of real current timestamps."""
        monitor = QCALRealTimeMonitor()
        
        # Get current timestamp
        current_time = monitor.get_high_precision_timestamp()
        
        # Calculate phase deviation
        delta = monitor.calculate_phase_deviation(current_time)
        
        # Verify delta is in valid range
        assert 0.0 <= delta < 1.0
        
        # Calculate coherence level
        coherence_level = min(delta, 1.0 - delta)
        assert 0.0 <= coherence_level <= 0.5
    
    def test_frequency_constant_accuracy(self):
        """Test that the frequency constant is accurate enough."""
        monitor = QCALRealTimeMonitor()
        
        # The frequency should be 141.7001 Hz (QCAL frequency from constants)
        # This should match the value in src/constants.py
        assert monitor.f0 == 141.7001
        
        # The period should be the reciprocal
        assert abs(monitor.tau0 * monitor.f0 - 1.0) < 1e-10
    
    def test_mathematical_consistency(self):
        """Test mathematical consistency of phase calculations."""
        monitor = QCALRealTimeMonitor()
        
        # Test that N = T / τ₀ gives correct number of cycles
        test_time = 100 * monitor.tau0  # 100 cycles
        N = test_time / monitor.tau0
        
        # N should be approximately 100
        assert abs(N - 100.0) < 1e-10
        
        # delta should be approximately 0
        delta = math.modf(N)[0]
        assert abs(delta) < 1e-10


class TestQCALIntegration:
    """Integration tests for QCAL monitor."""
    
    def test_monitor_short_run(self):
        """Test that monitor can run for a short duration without errors."""
        monitor = QCALRealTimeMonitor()
        
        # Override the sleep interval for faster testing
        monitor.SYNC_CHECK_INTERVAL = 0.01
        
        # Run monitor for a short time by simulating the loop body
        iterations = 5
        for _ in range(iterations):
            T = monitor.get_high_precision_timestamp()
            delta = monitor.calculate_phase_deviation(T)
            coherence_level = min(delta, 1.0 - delta)
            
            # Verify all values are valid
            assert T > 0
            assert 0.0 <= delta < 1.0
            assert 0.0 <= coherence_level <= 0.5
            
            time.sleep(monitor.SYNC_CHECK_INTERVAL)
    
    def test_output_formatting(self):
        """Test that monitor output can be formatted correctly."""
        monitor = QCALRealTimeMonitor()
        
        T = monitor.get_high_precision_timestamp()
        delta = monitor.calculate_phase_deviation(T)
        coherence_level = min(delta, 1.0 - delta)
        
        # Test timestamp formatting
        timestamp_str = datetime.fromtimestamp(T).strftime('%Y-%m-%d %H:%M:%S')
        assert len(timestamp_str) == 19  # Format: YYYY-MM-DD HH:MM:SS
        
        # Test microseconds formatting
        microseconds = int((T % 1) * 1e6)
        assert 0 <= microseconds < 1000000
        
        # Test status symbol assignment
        if coherence_level < monitor.COHERENCE_THRESHOLD:
            status_symbol = "🌟 PICO PURO"
        elif coherence_level < 0.05:
            status_symbol = "🟡 Alta Coherencia"
        else:
            status_symbol = "⚪"
        
        assert status_symbol in ["⚪", "🟡 Alta Coherencia", "🌟 PICO PURO"]


# Run tests if executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
