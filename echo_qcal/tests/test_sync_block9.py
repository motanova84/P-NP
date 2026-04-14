"""
Tests for Block 9 Synchrony Analysis

Validates the temporal synchrony calculations and statistical analysis
of Bitcoin Block 9's alignment with the QCAL ∞³ primordial frequency.
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from echo_qcal.block9_sync_analysis import (
    calculate_synchrony,
    analyze_block9_synchrony,
    verify_temporal_resonance
)
from echo_qcal.qcal_constants import F0, TAU0, T_BLOCK9, EPSILON


class TestBlock9Synchrony(unittest.TestCase):
    """Test cases for Block 9 synchrony analysis."""
    
    def test_calculate_synchrony_returns_dict(self):
        """Test that calculate_synchrony returns a dictionary."""
        results = calculate_synchrony()
        self.assertIsInstance(results, dict)
    
    def test_synchrony_contains_required_keys(self):
        """Test that synchrony results contain all required keys."""
        results = calculate_synchrony()
        
        required_keys = [
            'N_ideal', 'N_int', 'T_ideal', 'delta_T',
            'delta_T_ms', 'coherence', 'p_value', 'bayes_factor'
        ]
        
        for key in required_keys:
            self.assertIn(key, results)
    
    def test_delta_t_is_positive(self):
        """Test that delta_T is positive (absolute value)."""
        results = calculate_synchrony()
        self.assertGreater(results['delta_T'], 0)
    
    def test_delta_t_magnitude(self):
        """Test that delta_T is in expected range (milliseconds)."""
        results = calculate_synchrony()
        # Should be around 3.5 ms (0.0035 s)
        self.assertLess(results['delta_T'], 0.010)  # Less than 10 ms
        self.assertGreater(results['delta_T'], 0.001)  # More than 1 ms
    
    def test_coherence_is_high(self):
        """Test that coherence is very high (>99%)."""
        results = calculate_synchrony()
        self.assertGreater(results['coherence'], 99.0)
    
    def test_p_value_is_significant(self):
        """Test that p-value indicates statistical significance."""
        results = calculate_synchrony()
        self.assertLess(results['p_value'], 0.00001)  # p < 0.00001
    
    def test_bayes_factor_is_large(self):
        """Test that Bayes factor indicates strong evidence."""
        results = calculate_synchrony()
        self.assertGreater(results['bayes_factor'], 100000)  # > 100,000:1
    
    def test_ideal_cycles_calculation(self):
        """Test that ideal cycles calculation is correct."""
        results = calculate_synchrony()
        
        # Verify calculation: N_ideal = T_block9 / tau0
        expected_N_ideal = T_BLOCK9 / TAU0
        self.assertAlmostEqual(results['N_ideal'], expected_N_ideal, places=3)
    
    def test_integer_cycles(self):
        """Test that N_int is the rounded value of N_ideal."""
        results = calculate_synchrony()
        self.assertEqual(results['N_int'], round(results['N_ideal']))
    
    def test_ideal_timestamp_calculation(self):
        """Test that ideal timestamp is correctly calculated."""
        results = calculate_synchrony()
        
        # Verify: T_ideal = N_int * tau0
        expected_T_ideal = results['N_int'] * TAU0
        self.assertAlmostEqual(results['T_ideal'], expected_T_ideal, places=6)
    
    def test_delta_t_ms_conversion(self):
        """Test that delta_T_ms is correctly converted from seconds."""
        results = calculate_synchrony()
        self.assertAlmostEqual(
            results['delta_T_ms'],
            results['delta_T'] * 1000,
            places=3
        )
    
    def test_analyze_block9_synchrony_verbose(self):
        """Test that analyze_block9_synchrony runs without error."""
        results = analyze_block9_synchrony(verbose=False)
        self.assertIsInstance(results, dict)
        self.assertIn('delta_T', results)
    
    def test_verify_temporal_resonance(self):
        """Test temporal resonance verification."""
        is_resonant, explanation = verify_temporal_resonance()
        
        # Should return boolean and string
        self.assertIsInstance(is_resonant, bool)
        self.assertIsInstance(explanation, str)
        
        # Should be resonant (delta_T < EPSILON and p-value significant)
        self.assertTrue(is_resonant)
        self.assertIn('Block 9', explanation)
    
    def test_constants_are_valid(self):
        """Test that QCAL constants are valid."""
        self.assertGreater(F0, 0)
        self.assertGreater(TAU0, 0)
        self.assertGreater(T_BLOCK9, 0)
        self.assertGreater(EPSILON, 0)
        
        # Verify tau0 = 1/f0
        self.assertAlmostEqual(TAU0, 1.0 / F0, places=8)
    
    def test_synchrony_within_coherence_threshold(self):
        """Test that synchrony is within coherence threshold."""
        results = calculate_synchrony()
        self.assertLess(results['delta_T'], EPSILON)


class TestStatisticalMetrics(unittest.TestCase):
    """Test statistical metrics calculations."""
    
    def test_p_value_calculation(self):
        """Test p-value calculation matches expected formula."""
        from echo_qcal.qcal_constants import WINDOW
        
        results = calculate_synchrony()
        
        # P(random|H0) = (2 * epsilon) / window
        expected_p_value = (2 * EPSILON) / WINDOW
        self.assertAlmostEqual(results['p_value'], expected_p_value, places=10)
    
    def test_bayes_factor_calculation(self):
        """Test Bayes factor calculation."""
        from echo_qcal.qcal_constants import WINDOW
        
        results = calculate_synchrony()
        
        # Bayes factor = window / (2 * epsilon)
        expected_bayes = WINDOW / (2 * EPSILON)
        self.assertAlmostEqual(results['bayes_factor'], expected_bayes, places=1)
    
    def test_coherence_calculation(self):
        """Test coherence percentage calculation."""
        results = calculate_synchrony()
        
        # Coherence = (1 - delta_T / tau0) * 100
        expected_coherence = (1 - results['delta_T'] / TAU0) * 100
        self.assertAlmostEqual(results['coherence'], expected_coherence, places=4)


if __name__ == '__main__':
    unittest.main()
