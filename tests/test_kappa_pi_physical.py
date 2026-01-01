#!/usr/bin/env python3
"""
test_kappa_pi_physical.py - Tests for Physical κ_Π Computation

Tests the physical Calabi-Yau based computation of κ_Π = 2.5773.
"""

import sys
import os
import unittest
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from kappa_pi_physical import PhysicalKappaPi


class TestPhysicalKappaPi(unittest.TestCase):
    """Test cases for PhysicalKappaPi class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.kappa = PhysicalKappaPi()
        self.target_kappa = 2.5773
        self.tolerance = 0.01  # 1% tolerance
    
    def test_alpha_coupling(self):
        """Test α coupling computation."""
        vol_sigma3 = 5.0
        vol_cy = 12.5
        dilaton = 1.0
        
        alpha = self.kappa.compute_alpha(vol_sigma3, vol_cy, dilaton)
        
        # α should be positive and reasonable
        self.assertGreater(alpha, 0)
        self.assertLess(alpha, 1.0)
        
        # Check formula: α = (1/2π) · (vol_ratio) · e^(-ϕ)
        expected = (1.0 / (2 * np.pi)) * (vol_sigma3 / vol_cy) * np.exp(-dilaton)
        self.assertAlmostEqual(alpha, expected, places=10)
    
    def test_beta_coupling(self):
        """Test β coupling computation."""
        g_s = 0.1
        k = 3
        flux_integral = 2.0 * np.pi
        
        beta = self.kappa.compute_beta(g_s, k, flux_integral)
        
        # β should be positive and reasonable
        self.assertGreater(beta, 0)
        self.assertLess(beta, 1.0)
        
        # Check formula: β = (g_s/k) · flux_integral
        expected = (g_s / k) * flux_integral
        self.assertAlmostEqual(beta, expected, places=10)
    
    def test_beta_coupling_zero_k(self):
        """Test that β coupling raises error for k=0."""
        with self.assertRaises(ValueError):
            self.kappa.compute_beta(0.1, 0, 2.0 * np.pi)
    
    def test_rho_distribution_normalization(self):
        """Test that ρ(θ) integrates correctly with Z."""
        alpha = 0.3
        beta = 0.15
        n = 3
        m = 5
        
        # Compute Z
        Z = self.kappa.compute_normalization(alpha, beta, n, m)
        
        # Z should be close to 2π for normalized distribution
        self.assertGreater(Z, 0)
        
        # Verify normalization by manual integration
        from scipy import integrate
        
        def integrand(theta):
            return self.kappa.rho_distribution(theta, alpha, beta, n, m) / Z
        
        integral, _ = integrate.quad(integrand, 0, 2 * np.pi)
        
        # Should integrate to 1
        self.assertAlmostEqual(integral, 1.0, places=3)
    
    def test_entropy_functional_positive(self):
        """Test that entropy functional is positive."""
        alpha = 0.3
        beta = 0.15
        
        S_rho = self.kappa.entropy_functional(alpha, beta)
        
        # Differential entropy should be positive for this distribution
        self.assertGreater(S_rho, 0)
    
    def test_kappa_from_entropy(self):
        """Test full κ_Π computation from entropy."""
        alpha = 0.3
        beta = 0.15
        
        kappa_val = self.kappa.kappa_from_entropy(alpha, beta)
        
        # Should be positive and in reasonable range
        self.assertGreater(kappa_val, 0)
        self.assertLess(kappa_val, 10.0)
    
    def test_optimal_couplings_converge(self):
        """Test that optimal coupling search converges to target."""
        optimal = self.kappa.find_optimal_couplings()
        
        # Check that optimization succeeded
        self.assertTrue(optimal['success'])
        
        # Check that we're close to target
        error = abs(optimal['kappa_pi'] - self.target_kappa)
        self.assertLess(error, self.tolerance)
        
        # Check that α and β are in reasonable ranges
        self.assertGreater(optimal['alpha'], 0)
        self.assertLess(optimal['alpha'], 1.5)
        self.assertGreater(optimal['beta'], 0)
        self.assertLess(optimal['beta'], 1.5)
    
    def test_standard_cy3_example(self):
        """Test standard CY3 example produces correct κ_Π."""
        standard = self.kappa.standard_cy3_example()
        
        # Check that we get close to target
        computed_kappa = standard['kappa_pi']
        relative_error = abs(computed_kappa - self.target_kappa) / self.target_kappa
        
        self.assertLess(relative_error, self.tolerance)
        
        # Check that all physical parameters are present
        self.assertIn('vol_sigma3', standard['physical_input'])
        self.assertIn('vol_cy', standard['physical_input'])
        self.assertIn('dilaton', standard['physical_input'])
        self.assertIn('g_s', standard['physical_input'])
        self.assertIn('k', standard['physical_input'])
        self.assertIn('flux_integral', standard['physical_input'])
        
        # Check that couplings are present
        self.assertIn('alpha', standard['couplings'])
        self.assertIn('beta', standard['couplings'])
    
    def test_physical_parameters_to_kappa(self):
        """Test full computation from physical parameters."""
        vol_sigma3 = 5.0
        vol_cy = 12.5
        dilaton = 1.0
        g_s = 0.1
        k = 3
        flux_integral = 2.0 * np.pi
        
        result = self.kappa.physical_parameters_to_kappa(
            vol_sigma3, vol_cy, dilaton, g_s, k, flux_integral
        )
        
        # Should produce a valid κ_Π
        self.assertGreater(result['kappa_pi'], 0)
        self.assertLess(result['kappa_pi'], 10.0)
        
        # Check structure
        self.assertIn('physical_input', result)
        self.assertIn('couplings', result)
        self.assertIn('normalization', result)
        self.assertIn('entropy_S_rho', result)
        self.assertIn('kappa_pi', result)
    
    def test_reproducibility(self):
        """Test that computation is reproducible."""
        # Run same computation twice
        result1 = self.kappa.standard_cy3_example()
        result2 = self.kappa.standard_cy3_example()
        
        # Should give identical results
        self.assertEqual(result1['kappa_pi'], result2['kappa_pi'])
        self.assertEqual(result1['couplings']['alpha'], result2['couplings']['alpha'])
        self.assertEqual(result1['couplings']['beta'], result2['couplings']['beta'])
    
    def test_target_value_accuracy(self):
        """Test that we achieve the exact target value within tolerance."""
        optimal = self.kappa.find_optimal_couplings(target_kappa=2.5773)
        
        # Should be very close to 2.5773
        self.assertAlmostEqual(optimal['kappa_pi'], 2.5773, places=3)
        
        # Error should be less than 0.1%
        relative_error = abs(optimal['kappa_pi'] - 2.5773) / 2.5773
        self.assertLess(relative_error, 0.001)
    
    def test_different_frequency_modes(self):
        """Test that different frequency modes give different results."""
        kappa_3_5 = self.kappa.kappa_from_entropy(0.5, 0.2, n=3, m=5)
        kappa_4_6 = self.kappa.kappa_from_entropy(0.5, 0.2, n=4, m=6)
        
        # Different modes should give different results
        self.assertNotEqual(kappa_3_5, kappa_4_6)
    
    def test_extreme_parameters(self):
        """Test behavior with extreme parameter values."""
        # Very small α, β
        result_small = self.kappa.kappa_from_entropy(0.01, 0.01)
        self.assertGreater(result_small, 0)
        
        # Large α, β (within bounds)
        result_large = self.kappa.kappa_from_entropy(0.9, 0.7)
        self.assertGreater(result_large, 0)
        
        # Results should be different
        self.assertNotEqual(result_small, result_large)


class TestCalabiYauIntegration(unittest.TestCase):
    """Test integration with CalabiYauComplexity class."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Try to import CalabiYauComplexity
        try:
            from calabi_yau_complexity import CalabiYauComplexity
            self.cy = CalabiYauComplexity(use_physical_kappa=True)
            self.has_cy = True
        except ImportError:
            self.has_cy = False
    
    def test_calabi_yau_uses_physical_kappa(self):
        """Test that CalabiYauComplexity can use PhysicalKappaPi."""
        if not self.has_cy:
            self.skipTest("CalabiYauComplexity not available")
        
        # Should have physical kappa calculator
        self.assertIsNotNone(self.cy.physical_kappa)
        
        # kappa_pi should be close to target
        self.assertAlmostEqual(self.cy.kappa_pi, 2.5773, places=2)


def run_tests():
    """Run all tests."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalKappaPi))
    suite.addTests(loader.loadTestsFromTestCase(TestCalabiYauIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
