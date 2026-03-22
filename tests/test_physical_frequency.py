#!/usr/bin/env python3
"""
Test suite for physical_frequency.py module.
Validates the physical basis for fundamental frequency f₀.
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import unittest
import numpy as np
from physical_frequency import PhysicalFrequency, HYDROGEN_LINE, FINE_STRUCTURE


class TestPhysicalFrequency(unittest.TestCase):
    """Test cases for physical frequency calculations."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.pf = PhysicalFrequency()
    
    def test_fundamental_frequency_thermal_positive(self):
        """f₀ from thermal calculation must be positive."""
        f0_thermal = self.pf.calculate_f0_thermal()
        self.assertGreater(f0_thermal, 0)
    
    def test_fundamental_frequency_thermal_range(self):
        """f₀ thermal should be in expected range ~5.7×10¹⁰ Hz."""
        f0_thermal = self.pf.calculate_f0_thermal()
        self.assertGreater(f0_thermal, 5.6e10)
        self.assertLess(f0_thermal, 5.8e10)
    
    def test_fundamental_frequency_atomic_positive(self):
        """f₀ from atomic calculation must be positive."""
        f0_atomic = self.pf.calculate_f0_atomic()
        self.assertGreater(f0_atomic, 0)
    
    def test_fundamental_frequency_atomic_range(self):
        """f₀ atomic should be approximately 141.7 Hz."""
        f0_atomic = self.pf.calculate_f0_atomic()
        self.assertGreater(f0_atomic, 140)
        self.assertLess(f0_atomic, 143)
        # More precise check
        self.assertAlmostEqual(f0_atomic, 141.7001, places=4)
    
    def test_frequency_scales_separated(self):
        """Thermal and atomic frequencies should be vastly different."""
        f0_thermal = self.pf.calculate_f0_thermal()
        f0_atomic = self.pf.calculate_f0_atomic()
        ratio = f0_thermal / f0_atomic
        self.assertGreater(ratio, 1e6)
    
    def test_hydrogen_connection(self):
        """f₀ should relate to hydrogen 21-cm line."""
        f0_atomic = self.pf.calculate_f0_atomic()
        # Should be many orders of magnitude smaller than hydrogen line
        self.assertLess(f0_atomic, HYDROGEN_LINE / 1e6)
    
    def test_experimental_validation_passes(self):
        """Experimental validation should find reasonable harmonics."""
        results = self.pf.experimental_validation()
        self.assertIn('validates', results)
        self.assertIn('coherence_score', results)
        # At least some neural frequencies should be near harmonics
        self.assertGreaterEqual(results['coherence_score'], 0.2)
    
    def test_harmonic_relationships(self):
        """Check specific harmonic relationships with neural frequencies."""
        f0_atomic = self.pf.calculate_f0_atomic()
        results = self.pf.experimental_validation()
        
        # Check that we have harmonic data
        self.assertIn('harmonics', results)
        harmonics = results['harmonics']
        
        # At least one band should have near-integer ratio
        near_integer_count = sum(1 for h in harmonics.values() if h['near_integer'])
        self.assertGreater(near_integer_count, 0)
    
    def test_spectral_analysis_basic(self):
        """Basic spectral analysis should work on sample data."""
        # Create sample eigenvalues (like a 3-regular expander)
        eigenvalues = np.array([3.0, 1.5, 0.5, -0.5, -1.5, -2.0])
        
        results = self.pf.spectral_analysis_connection(eigenvalues)
        
        # Check required keys
        self.assertIn('spectral_gap', results)
        self.assertIn('max_eigenvalue', results)
        self.assertIn('resonance_strength', results)
        
        # Spectral gap should be positive for this example
        self.assertGreater(results['spectral_gap'], 0)
    
    def test_validate_against_measurements(self):
        """All physical validation checks should pass."""
        results = self.pf.validate_against_measurements()
        
        # Check all individual validations pass
        self.assertTrue(results['f0_thermal_positive'])
        self.assertTrue(results['f0_thermal_range'])
        self.assertTrue(results['f0_atomic_positive'])
        self.assertTrue(results['f0_atomic_range'])
        self.assertTrue(results['scales_separated'])
        self.assertTrue(results['hydrogen_connection'])
        
        # Overall should pass
        self.assertTrue(results['all_validations_pass'])
    
    def test_summary_report_generation(self):
        """Summary report should generate without errors."""
        report = self.pf.summary_report()
        self.assertIsInstance(report, str)
        self.assertGreater(len(report), 100)
        # Check for key sections
        self.assertIn('Physical Frequency', report)
        self.assertIn('f₀ (thermal)', report)
        self.assertIn('f₀ (atomic)', report)
    
    def test_physical_constants_reasonable(self):
        """Check that physical constants are in reasonable ranges."""
        # Planck's constant (J·s)
        self.assertGreater(self.pf.h_bar, 1e-35)
        self.assertLess(self.pf.h_bar, 1e-33)
        
        # Boltzmann constant (J/K)
        self.assertGreater(self.pf.k_B, 1e-24)
        self.assertLess(self.pf.k_B, 1e-22)
        
        # CMB temperature (K)
        self.assertGreater(self.pf.T_c, 2)
        self.assertLess(self.pf.T_c, 3)
        
        # Fine structure constant (dimensionless)
        self.assertGreater(self.pf.alpha, 1/138)
        self.assertLess(self.pf.alpha, 1/136)


class TestFrequencyReproducibility(unittest.TestCase):
    """Test reproducibility and consistency of frequency calculations."""
    
    def test_thermal_frequency_deterministic(self):
        """Thermal frequency calculation should be deterministic."""
        pf1 = PhysicalFrequency()
        pf2 = PhysicalFrequency()
        
        f0_1 = pf1.calculate_f0_thermal()
        f0_2 = pf2.calculate_f0_thermal()
        
        self.assertEqual(f0_1, f0_2)
    
    def test_atomic_frequency_deterministic(self):
        """Atomic frequency calculation should be deterministic."""
        pf1 = PhysicalFrequency()
        pf2 = PhysicalFrequency()
        
        f0_1 = pf1.calculate_f0_atomic()
        f0_2 = pf2.calculate_f0_atomic()
        
        self.assertEqual(f0_1, f0_2)
    
    def test_validation_consistent(self):
        """Validation results should be consistent across runs."""
        pf = PhysicalFrequency()
        
        results1 = pf.validate_against_measurements()
        results2 = pf.validate_against_measurements()
        
        self.assertEqual(results1, results2)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and error handling."""
    
    def test_empty_eigenvalues(self):
        """Spectral analysis should handle empty input gracefully."""
        pf = PhysicalFrequency()
        eigenvalues = np.array([])
        
        # Should not crash
        try:
            results = pf.spectral_analysis_connection(eigenvalues)
            # If it doesn't crash, check it returns a dict
            self.assertIsInstance(results, dict)
        except Exception as e:
            # If it does raise an exception, it should be a reasonable one
            self.assertIsInstance(e, (ValueError, ZeroDivisionError))
    
    def test_single_eigenvalue(self):
        """Spectral analysis with single eigenvalue."""
        pf = PhysicalFrequency()
        eigenvalues = np.array([1.0])
        
        results = pf.spectral_analysis_connection(eigenvalues)
        self.assertIn('spectral_gap', results)
        # Gap should be 0 for single eigenvalue
        self.assertEqual(results['spectral_gap'], 0.0)


def run_tests():
    """Run all tests and return results."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalFrequency))
    suite.addTests(loader.loadTestsFromTestCase(TestFrequencyReproducibility))
    suite.addTests(loader.loadTestsFromTestCase(TestEdgeCases))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
