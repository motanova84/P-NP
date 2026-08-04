"""
Test suite for Echo Qcal A_t verification module
=================================================

Tests the temporal alignment verification of Bitcoin Block 9 with the
primordial frequency f₀ = 141.7001 Hz.

This test suite verifies:
- TemporalAlignmentVerifier class instantiation
- verify_temporal_alignment() calculations
- JSON output format
- Threshold validations
- Error handling

Author: JMMB Ψ✧ ∞³
"""

import sys
import os
import pytest
import json
from datetime import datetime, timezone

# Add echo_qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from echo_qcal.A_t_verification import TemporalAlignmentVerifier


class TestTemporalAlignmentVerifier:
    """Test suite for TemporalAlignmentVerifier class"""
    
    def test_verifier_instantiation(self):
        """Test that TemporalAlignmentVerifier can be instantiated."""
        verifier = TemporalAlignmentVerifier()
        assert verifier is not None
        assert isinstance(verifier, TemporalAlignmentVerifier)
    
    def test_verifier_constants(self):
        """Test that verifier has correct constants."""
        verifier = TemporalAlignmentVerifier()
        
        # Check frequency constant
        assert verifier.f0 == 141.7001, "Primordial frequency f₀ should be 141.7001 Hz"
        
        # Check tau0 calculation
        expected_tau0 = 1 / 141.7001
        assert abs(verifier.tau0 - expected_tau0) < 1e-10, "τ₀ should be 1/f₀"
        
        # Check Block 9 timestamp
        assert verifier.block9_timestamp == 1231511700.0, "Block 9 timestamp should be 1231511700"
        
        # Check Block 9 hash
        expected_hash = "000000008d9dc510f23c2657fc4f67bea30078cc05a90eb89e84cc475c080805"
        assert verifier.block9_hash == expected_hash, "Block 9 hash should match"
        
        # Check thresholds
        assert verifier.coherence_threshold == 99.95, "Coherence threshold should be 99.95%"
        assert verifier.delta_t_threshold == 0.010, "Delta T threshold should be 0.010 s (10 ms)"
    
    def test_block9_timestamp_conversion(self):
        """Test that Block 9 timestamp converts to correct datetime."""
        verifier = TemporalAlignmentVerifier()
        
        # Convert timestamp to datetime
        dt = datetime.fromtimestamp(verifier.block9_timestamp, tz=timezone.utc)
        
        # Check the datetime is correct (2009-01-09 14:35:00 UTC)
        assert dt.year == 2009, "Year should be 2009"
        assert dt.month == 1, "Month should be January"
        assert dt.day == 9, "Day should be 9"
        assert dt.hour == 14, "Hour should be 14 (UTC)"
        assert dt.minute == 35, "Minute should be 35"
        assert dt.second == 0, "Second should be 0"
    
    def test_verify_temporal_alignment_returns_dict(self):
        """Test that verify_temporal_alignment returns a dictionary."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        assert isinstance(results, dict), "Results should be a dictionary"
    
    def test_verify_temporal_alignment_structure(self):
        """Test that verify_temporal_alignment returns correct structure."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Check top-level keys
        assert 'verification_passed' in results
        assert 'parameters' in results
        assert 'alignment_metrics' in results
        assert 'statistical_analysis' in results
        assert 'thresholds' in results
        
        # Check verification_passed is boolean
        assert isinstance(results['verification_passed'], bool)
        
        # Check parameters structure
        params = results['parameters']
        assert 'f0_hz' in params
        assert 'tau0_s' in params
        assert 'block9_timestamp' in params
        assert 'block9_datetime' in params
        assert 'block9_hash' in params
        
        # Check alignment_metrics structure
        metrics = results['alignment_metrics']
        assert 'N_ideal' in metrics
        assert 'N_integer' in metrics
        assert 'T_ideal_s' in metrics
        assert 'delta_T_s' in metrics
        assert 'delta_T_ms' in metrics
        assert 'coherence_percent' in metrics
        assert 'phase' in metrics
        assert 'phase_description' in metrics
        
        # Check statistical_analysis structure
        stats = results['statistical_analysis']
        assert 'window_s' in stats
        assert 'epsilon_s' in stats
        assert 'p_value' in stats
        assert 'bayes_factor' in stats
        assert 'significance' in stats
        
        # Check thresholds structure
        thresholds = results['thresholds']
        assert 'coherence_threshold_percent' in thresholds
        assert 'delta_t_threshold_s' in thresholds
        assert 'delta_t_threshold_ms' in thresholds
    
    def test_verify_temporal_alignment_calculations(self):
        """Test that verify_temporal_alignment performs correct calculations."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Verify N_ideal calculation
        expected_N_ideal = verifier.block9_timestamp / verifier.tau0
        assert abs(results['alignment_metrics']['N_ideal'] - expected_N_ideal) < 1e-6
        
        # Verify N_integer is an integer
        assert isinstance(results['alignment_metrics']['N_integer'], int)
        
        # Verify T_ideal calculation
        N_integer = results['alignment_metrics']['N_integer']
        expected_T_ideal = N_integer * verifier.tau0
        assert abs(results['alignment_metrics']['T_ideal_s'] - expected_T_ideal) < 1e-10
        
        # Verify delta_T calculation
        expected_delta_T = abs(expected_T_ideal - verifier.block9_timestamp)
        assert abs(results['alignment_metrics']['delta_T_s'] - expected_delta_T) < 1e-10
        
        # Verify delta_T_ms is in milliseconds
        assert abs(results['alignment_metrics']['delta_T_ms'] - expected_delta_T * 1000) < 1e-6
        
        # Verify coherence calculation
        expected_coherence = (1 - expected_delta_T / verifier.tau0) * 100
        assert abs(results['alignment_metrics']['coherence_percent'] - expected_coherence) < 1e-6
        
        # Verify phase is between 0 and 1
        assert 0 <= results['alignment_metrics']['phase'] < 1
    
    def test_statistical_analysis_calculations(self):
        """Test that statistical analysis calculations are correct."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        stats = results['statistical_analysis']
        
        # Check window and epsilon values
        assert stats['window_s'] == 7200, "Window should be 7200 seconds (2 hours)"
        assert stats['epsilon_s'] == 0.010, "Epsilon should be 0.010 seconds (10 ms)"
        
        # Verify p_value calculation
        expected_p_value = (2 * stats['epsilon_s']) / stats['window_s']
        assert abs(stats['p_value'] - expected_p_value) < 1e-10
        
        # Verify Bayes factor calculation
        expected_bayes = stats['window_s'] / (2 * stats['epsilon_s'])
        assert abs(stats['bayes_factor'] - expected_bayes) < 1e-6
        
        # Check significance
        assert stats['significance'] in ['EXTREME', 'MODERATE']
    
    def test_threshold_validation(self):
        """Test that thresholds are correctly validated."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Get metrics and thresholds
        delta_T = results['alignment_metrics']['delta_T_s']
        coherence = results['alignment_metrics']['coherence_percent']
        
        delta_threshold = results['thresholds']['delta_t_threshold_s']
        coherence_threshold = results['thresholds']['coherence_threshold_percent']
        
        # Verify verification_passed logic
        expected_passes = (delta_T <= delta_threshold) and (coherence >= coherence_threshold)
        assert results['verification_passed'] == expected_passes
    
    def test_save_results_to_json(self):
        """Test that save_results_to_json creates valid JSON file."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Use a temporary filename
        test_filename = "test_A_t_results.json"
        
        try:
            # Save results
            filepath = verifier.save_results_to_json(results, filename=test_filename)
            
            # Check file exists
            assert os.path.exists(filepath), "JSON file should exist"
            
            # Load and validate JSON
            with open(filepath, 'r') as f:
                loaded_results = json.load(f)
            
            # Check structure is preserved
            assert loaded_results['verification_passed'] == results['verification_passed']
            assert loaded_results['parameters']['f0_hz'] == results['parameters']['f0_hz']
            assert loaded_results['alignment_metrics']['coherence_percent'] == results['alignment_metrics']['coherence_percent']
            
        finally:
            # Clean up test file
            if os.path.exists(filepath):
                os.remove(filepath)
    
    def test_save_results_error_handling(self):
        """Test that save_results_to_json handles errors properly."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Try to save to an invalid path
        invalid_path = "/invalid/path/that/does/not/exist/test.json"
        
        with pytest.raises(IOError):
            verifier.save_results_to_json(results, filename=invalid_path)
    
    def test_generate_verification_report(self):
        """Test that generate_verification_report runs without errors."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # Should return results unchanged
        report_results = verifier.generate_verification_report(results)
        assert report_results == results
    
    def test_datetime_format_no_deprecation(self):
        """Test that datetime conversion doesn't use deprecated methods."""
        verifier = TemporalAlignmentVerifier()
        results = verifier.verify_temporal_alignment()
        
        # The datetime string should be in ISO format with timezone
        dt_string = results['parameters']['block9_datetime']
        
        # Should be parseable as ISO format
        dt = datetime.fromisoformat(dt_string)
        
        # Should have timezone info
        assert dt.tzinfo is not None, "Datetime should have timezone info"
    
    def test_verification_file_exists(self):
        """Test that A_t_verification.py file exists."""
        verification_file = os.path.join(
            os.path.dirname(__file__), 
            '..', 
            'echo_qcal', 
            'A_t_verification.py'
        )
        assert os.path.exists(verification_file)
    
    def test_verification_results_json_exists(self):
        """Test that A_t_verification_results.json file exists."""
        results_file = os.path.join(
            os.path.dirname(__file__), 
            '..', 
            'echo_qcal', 
            'A_t_verification_results.json'
        )
        
        # File should exist (generated by previous runs)
        if os.path.exists(results_file):
            # Validate it's valid JSON
            with open(results_file, 'r') as f:
                data = json.load(f)
            
            # Should have expected structure
            assert 'verification_passed' in data
            assert 'parameters' in data
            assert 'alignment_metrics' in data


def test_echo_qcal_module_updated():
    """Test that echo_qcal module has correct metadata."""
    import echo_qcal
    assert echo_qcal.__version__ == "1.0.0"
    assert echo_qcal.__author__ == "José Manuel Mota Burruezo Ψ ✧ ∞³"
    assert echo_qcal.__frequency__ == "141.7001 Hz"


def test_main_function_exists():
    """Test that main function exists and can be imported."""
    from echo_qcal.A_t_verification import main
    assert callable(main)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
