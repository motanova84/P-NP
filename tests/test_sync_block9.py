#!/usr/bin/env python3
"""
Test suite for Block 9 synchrony analysis.

Tests the temporal resonance validation between Bitcoin Block 9
and the QCAL universal frequency.
"""

import pytest
import sys
import os

# Add echo_qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from echo_qcal.block9_sync_analysis import QCALSyncAnalyzer


class TestQCALSyncAnalyzer:
    """Test suite for QCAL synchrony analyzer."""
    
    @pytest.fixture
    def analyzer(self):
        """Create a QCALSyncAnalyzer instance."""
        return QCALSyncAnalyzer()
    
    def test_analyzer_initialization(self, analyzer):
        """Test that analyzer initializes with correct parameters."""
        assert analyzer.f0 == 141.7001
        assert abs(analyzer.tau0 - (1.0 / 141.7001)) < 1e-10
    
    def test_coherence_period(self, analyzer):
        """Test that coherence period is calculated correctly."""
        tau0_ms = analyzer.tau0 * 1000
        # Should be approximately 7.0569 ms
        assert 7.0 < tau0_ms < 7.1
    
    def test_block9_analysis_structure(self, analyzer):
        """Test that Block 9 analysis returns correct structure."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        # Check all required keys are present
        required_keys = [
            'block9_timestamp',
            'block9_datetime',
            'qcal_frequency_hz',
            'coherence_period_s',
            'coherence_period_ms',
            'cycles_count',
            'nearest_coherent_time',
            'delta_t_seconds',
            'delta_t_milliseconds',
            'p_value',
            'is_synchronized',
            'significance'
        ]
        
        for key in required_keys:
            assert key in results, f"Missing key: {key}"
    
    def test_block9_timestamp_value(self, analyzer):
        """Test that Block 9 timestamp is correct."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        assert results['block9_timestamp'] == BLOCK9_TIMESTAMP
    
    def test_block9_frequency(self, analyzer):
        """Test that QCAL frequency is correct."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        assert results['qcal_frequency_hz'] == 141.7001
    
    def test_block9_cycles_count(self, analyzer):
        """Test that cycle count is reasonable."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        # Should be approximately 174.5 billion cycles
        cycles = results['cycles_count']
        assert 174_000_000_000 < cycles < 175_000_000_000
    
    def test_block9_synchronization(self, analyzer):
        """Test that Block 9 shows temporal synchronization."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        # Delta T should be small (< 10 ms based on analysis)
        delta_t_ms = results['delta_t_milliseconds']
        assert delta_t_ms < 10.0, f"Delta T too large: {delta_t_ms} ms"
    
    def test_block9_low_probability(self, analyzer):
        """Test that Block 9 synchrony has low random probability."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        # P-value should be very small (< 0.01)
        p_value = results['p_value']
        assert p_value < 0.01, f"P-value too high: {p_value}"
    
    def test_resonance_probability_calculation(self, analyzer):
        """Test the resonance probability calculation."""
        # Test with known values
        prob_1ms = analyzer.calculate_resonance_probability(1.0)
        prob_5ms = analyzer.calculate_resonance_probability(5.0)
        
        # Higher deviation should give higher probability
        assert prob_5ms > prob_1ms
        
        # Probabilities should be between 0 and 1
        assert 0 <= prob_1ms <= 1
        assert 0 <= prob_5ms <= 1
    
    def test_different_timestamps(self, analyzer):
        """Test analysis with different timestamps."""
        # Test with a few different timestamps
        timestamps = [
            1231469665,  # Block 9
            1231006505,  # Block 0 (Genesis)
            1609459200,  # 2021-01-01 00:00:00 UTC
        ]
        
        for ts in timestamps:
            results = analyzer.analyze_block9_sync(ts)
            
            # Should always return valid structure
            assert 'delta_t_milliseconds' in results
            assert 'p_value' in results
            assert isinstance(results['cycles_count'], int)
    
    def test_significance_status(self, analyzer):
        """Test that significance status is assigned correctly."""
        BLOCK9_TIMESTAMP = 1231469665
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        
        if results['delta_t_milliseconds'] < 5.0:
            assert results['significance'] == 'CONFIRMED'
            assert results['is_synchronized'] is True
        else:
            assert results['significance'] == 'INCONCLUSIVE'


class TestBlockSyncIntegration:
    """Integration tests for the complete block sync analysis."""
    
    def test_main_execution(self):
        """Test that main() executes without errors."""
        from echo_qcal.block9_sync_analysis import main
        
        # Should execute and return results
        results = main()
        
        assert results is not None
        assert 'significance' in results
    
    def test_temporal_deviation_formula(self):
        """Test the temporal deviation formula implementation."""
        analyzer = QCALSyncAnalyzer()
        BLOCK9_TIMESTAMP = 1231469665
        
        # Manually calculate expected deviation
        tau0 = analyzer.tau0
        cycles = round(BLOCK9_TIMESTAMP / tau0)
        nearest_time = cycles * tau0
        expected_delta = abs(BLOCK9_TIMESTAMP - nearest_time)
        
        # Compare with analyzer result
        results = analyzer.analyze_block9_sync(BLOCK9_TIMESTAMP)
        actual_delta = results['delta_t_seconds']
        
        # Should match within floating point precision
        assert abs(expected_delta - actual_delta) < 1e-9


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
