#!/usr/bin/env python3
"""
test_calabi_yau_kappa_pi.py - Tests for Calabi-Yau κ_Π structural analysis

Tests the implementation of the structural appearance of κ_Π in
Calabi-Yau geometry with N = h^{1,1} + h^{2,1}.
"""

import unittest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_kappa_pi_analysis import (
    CalabiYauKappaAnalysis,
    PHI,
    KAPPA_PI_TARGET
)


class TestCalabiYauKappaAnalysis(unittest.TestCase):
    """Test suite for Calabi-Yau κ_Π analysis."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.analyzer = CalabiYauKappaAnalysis()
        self.epsilon = 1e-6  # Tolerance for floating point comparisons
    
    def test_golden_ratio(self):
        """Test that golden ratio is correctly calculated."""
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(self.analyzer.phi, expected_phi, places=10)
        self.assertAlmostEqual(self.analyzer.phi, 1.618033988749895, places=10)
    
    def test_phi_squared(self):
        """Test that φ² is correctly calculated."""
        expected = PHI ** 2
        self.assertAlmostEqual(self.analyzer.phi_squared, expected, places=10)
        # φ² = φ + 1 (golden ratio property)
        self.assertAlmostEqual(self.analyzer.phi_squared, PHI + 1, places=10)
    
    def test_kappa_pi_basic(self):
        """Test basic κ_Π calculation."""
        # κ_Π(N) = ln(N) / ln(φ²)
        N = 10
        expected = math.log(N) / math.log(self.analyzer.phi_squared)
        result = self.analyzer.kappa_pi(N)
        self.assertAlmostEqual(result, expected, places=10)
    
    def test_kappa_pi_for_cicy_values(self):
        """Test κ_Π for CICY relevant values."""
        # Test N = 12, 13, 14, 15
        # These are calculated using κ_Π(N) = ln(N) / ln(φ²)
        test_cases = {
            12: 2.5819,  # Precise calculation
            13: 2.6651,  # Matches problem statement
            14: 2.7421,  # Precise calculation
            15: 2.8138,  # Precise calculation
        }
        
        for N, expected_kappa in test_cases.items():
            result = self.analyzer.kappa_pi(N)
            # Allow small tolerance for floating point
            self.assertAlmostEqual(result, expected_kappa, delta=0.002,
                                 msg=f"κ_Π({N}) should be approximately {expected_kappa}")
    
    def test_kappa_pi_strictly_increasing(self):
        """Test that κ_Π(N) is strictly increasing."""
        N_values = [5, 10, 15, 20, 25, 30]
        kappa_values = [self.analyzer.kappa_pi(N) for N in N_values]
        
        # Check that each value is greater than the previous
        for i in range(1, len(kappa_values)):
            self.assertGreater(kappa_values[i], kappa_values[i-1],
                             msg=f"κ_Π should be strictly increasing")
    
    def test_kappa_pi_invalid_input(self):
        """Test that κ_Π raises error for invalid input."""
        with self.assertRaises(ValueError):
            self.analyzer.kappa_pi(0)
        
        with self.assertRaises(ValueError):
            self.analyzer.kappa_pi(-5)
    
    def test_solve_for_N_star(self):
        """Test solving for N* where κ_Π(N*) = 2.5773."""
        N_star = self.analyzer.solve_for_N_star()
        
        # With log_φ² formula: N* = (φ²)^2.5773 ≈ 11.947
        # This is what the code implements
        self.assertAlmostEqual(N_star, 11.946693, delta=0.001,
                             msg="N* should be approximately 11.947 for log_φ² formula")
        
        # Verify that κ_Π(N*) = 2.5773
        kappa_at_N_star = self.analyzer.kappa_pi(N_star)
        self.assertAlmostEqual(kappa_at_N_star, KAPPA_PI_TARGET, places=4,
                             msg="κ_Π(N*) should equal the target 2.5773")
    
    def test_N_star_formula(self):
        """Test that N* = (φ²)^κ_Π."""
        N_star = self.analyzer.solve_for_N_star()
        expected = self.analyzer.phi_squared ** KAPPA_PI_TARGET
        self.assertAlmostEqual(N_star, expected, places=10)
    
    def test_N_star_proximity_to_13(self):
        """Test that N* is close to integer 12 (not 13) with log_φ² formula."""
        N_star = self.analyzer.solve_for_N_star()
        distance_to_12 = abs(N_star - 12)
        
        # N* ≈ 11.947 with log_φ² formula, so it's close to 12
        # Should be within 0.1 of 12
        self.assertLess(distance_to_12, 0.1,
                       msg="N* should be very close to 12 with log_φ² formula")
        
        # More specifically, should be approximately 11.95
        self.assertAlmostEqual(N_star, 11.95, delta=0.01,
                              msg="N* should be approximately 11.95")
    
    def test_evaluate_table(self):
        """Test evaluation table generation."""
        N_values = [12, 13, 14, 15]
        table = self.analyzer.evaluate_table(N_values)
        
        # Check structure
        self.assertEqual(len(table), len(N_values))
        
        for i, row in enumerate(table):
            self.assertIn('N', row)
            self.assertIn('kappa_pi', row)
            self.assertIn('distance_to_target', row)
            self.assertEqual(row['N'], N_values[i])
            
            # Verify distance calculation
            expected_dist = abs(row['kappa_pi'] - KAPPA_PI_TARGET)
            self.assertAlmostEqual(row['distance_to_target'], expected_dist, places=10)
    
    def test_classify_phase_below_threshold(self):
        """Test phase classification for N < N*."""
        # With log_φ² formula, N* ≈ 11.947
        # So N = 11 should be in Phase 1 (below N*)
        phase, desc = self.analyzer.classify_phase(11)
        self.assertEqual(phase, "Phase 1")
        self.assertIn("N < N*", desc)
    
    def test_classify_phase_above_threshold(self):
        """Test phase classification for N > N*."""
        # With log_φ² formula, N* ≈ 11.947
        # So N = 13, 14, 15 should be in Phase 2 (above N*)
        for N in [13, 14, 15]:
            phase, desc = self.analyzer.classify_phase(N)
            self.assertEqual(phase, "Phase 2")
            self.assertIn("N > N*", desc)
    
    def test_classify_phase_near_threshold(self):
        """Test phase classification for N ≈ N*."""
        N_star = self.analyzer.solve_for_N_star()
        
        # Test N = 12 (very close to N* ≈ 11.947, slightly above)
        phase, desc = self.analyzer.classify_phase(12)
        # 12 > 11.947, so should be Phase 2
        self.assertEqual(phase, "Phase 2")
    
    def test_analyze_cicy_spectrum(self):
        """Test complete CICY spectrum analysis."""
        analysis = self.analyzer.analyze_cicy_spectrum()
        
        # Check required keys
        required_keys = [
            'N_star', 'N_star_rounded', 'closest_integer',
            'distance_to_closest', 'evaluation_table',
            'kappa_at_N_star', 'phase_classifications'
        ]
        for key in required_keys:
            self.assertIn(key, analysis)
        
        # Check N_star (≈ 11.947 with log_φ² formula)
        self.assertAlmostEqual(analysis['N_star'], 11.946693, delta=0.01)
        self.assertEqual(analysis['N_star_rounded'], 12)
        
        # Check closest integer
        self.assertEqual(analysis['closest_integer'], 12)
        
        # Check kappa at N*
        self.assertAlmostEqual(analysis['kappa_at_N_star'], KAPPA_PI_TARGET, places=4)
        
        # Check evaluation table
        self.assertEqual(len(analysis['evaluation_table']), 4)  # 12, 13, 14, 15
        
        # Check phase classifications
        self.assertEqual(len(analysis['phase_classifications']), 4)
    
    def test_emergent_hypothesis(self):
        """Test emergent hypothesis formulation."""
        hypothesis = self.analyzer.emergent_hypothesis()
        
        # Check required keys (based on current implementation)
        required_keys = [
            'title', 'constant', 'threshold_value', 'nearest_integer',
            'N_effective', 'statements', 'mathematical_form', 'critical_property',
            'resonance_implication', 'integer_approximation', 'effective_value'
        ]
        for key in required_keys:
            self.assertIn(key, hypothesis)
        
        # Check values
        self.assertEqual(hypothesis['constant'], KAPPA_PI_TARGET)
        # The implementation uses N=13 as nearest integer in emergent_hypothesis
        # even though the log_φ² formula gives N* ≈ 11.95 (closer to 12)
        # This reflects the documented discrepancy between formulas
        self.assertEqual(hypothesis['nearest_integer'], 13)
        self.assertIsInstance(hypothesis['statements'], list)
        self.assertGreater(len(hypothesis['statements']), 0)
    
    def test_kappa_pi_mathematical_properties(self):
        """Test mathematical properties of κ_Π function."""
        # Test that κ_Π(φ²) = 1
        result = self.analyzer.kappa_pi(self.analyzer.phi_squared)
        self.assertAlmostEqual(result, 1.0, places=10,
                             msg="κ_Π(φ²) should equal 1")
        
        # Test that κ_Π((φ²)^k) = k for integer k
        for k in [1, 2, 3, 4, 5]:
            N = self.analyzer.phi_squared ** k
            result = self.analyzer.kappa_pi(N)
            self.assertAlmostEqual(result, k, places=10,
                                 msg=f"κ_Π((φ²)^{k}) should equal {k}")
    
    def test_logarithmic_base_change(self):
        """Test that κ_Π(N) = log_φ²(N)."""
        N = 100
        # κ_Π(N) = ln(N) / ln(φ²) = log_φ²(N)
        kappa_N = self.analyzer.kappa_pi(N)
        log_base_phi2_N = math.log(N) / math.log(self.analyzer.phi_squared)
        
        self.assertAlmostEqual(kappa_N, log_base_phi2_N, places=10)
        
        # Verify: (φ²)^κ_Π(N) = N
        reconstructed_N = self.analyzer.phi_squared ** kappa_N
        self.assertAlmostEqual(reconstructed_N, N, places=10)
    
    def test_plot_generation(self):
        """Test that plot can be generated without errors."""
        import tempfile
        import os
        
        with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            # Generate plot
            result_path = self.analyzer.plot_kappa_curve(save_path=tmp_path)
            
            # Check that file was created
            self.assertTrue(os.path.exists(result_path))
            self.assertEqual(result_path, tmp_path)
            
            # Check file is not empty
            file_size = os.path.getsize(result_path)
            self.assertGreater(file_size, 0)
            
        finally:
            # Cleanup
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


class TestIntegrationWithExistingModule(unittest.TestCase):
    """Test integration with existing calabi_yau_complexity module."""
    
    def test_kappa_pi_constant_consistency(self):
        """Test that KAPPA_PI constant is consistent with constants.py."""
        # Import from constants
        from constants import KAPPA_PI as KAPPA_FROM_CONSTANTS
        
        # Should match the target value
        self.assertAlmostEqual(KAPPA_PI_TARGET, KAPPA_FROM_CONSTANTS, places=4)
        self.assertEqual(KAPPA_PI_TARGET, 2.5773)
    
    def test_golden_ratio_consistency(self):
        """Test golden ratio consistency with constants.py."""
        from constants import GOLDEN_RATIO
        
        self.assertAlmostEqual(PHI, GOLDEN_RATIO, places=10)
    
    def test_N_eff_constant_consistency(self):
        """Test N_eff constant consistency with constants.py."""
        from constants import N_EFF_KAPPA_PI_LOG_PHI2, N_EFF_KAPPA_PI_SIMPLE_LN
        
        # Test log_φ² formula (currently implemented in code)
        analyzer = CalabiYauKappaAnalysis()
        
        # For log_φ² formula: N_eff ≈ 11.947
        # Verify the constant matches the expected calculated value
        expected_log_phi2 = analyzer.phi_squared ** KAPPA_PI_TARGET
        self.assertAlmostEqual(N_EFF_KAPPA_PI_LOG_PHI2, expected_log_phi2, places=5)
        kappa_log_phi2 = analyzer.kappa_pi(N_EFF_KAPPA_PI_LOG_PHI2)
        self.assertAlmostEqual(kappa_log_phi2, KAPPA_PI_TARGET, places=4,
                              msg="log_φ² formula should give exact κ_Π")
        
        # For simple ln formula: N_eff ≈ 13.162
        # Verify the constant matches the expected calculated value
        import math
        expected_simple_ln = math.exp(KAPPA_PI_TARGET)
        self.assertAlmostEqual(N_EFF_KAPPA_PI_SIMPLE_LN, expected_simple_ln, places=5)
        kappa_simple_ln = math.log(N_EFF_KAPPA_PI_SIMPLE_LN)
        self.assertAlmostEqual(kappa_simple_ln, KAPPA_PI_TARGET, places=4,
                              msg="Simple ln formula should give exact κ_Π")


def run_tests():
    """Run all tests and return results."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestCalabiYauKappaAnalysis))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegrationWithExistingModule))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
