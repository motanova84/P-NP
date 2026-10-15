#!/usr/bin/env python3
"""
Tests for advanced frequency dimension extensions.

Tests new functionality:
- spectral_sweep_analysis
- monte_carlo_validation
- optimize_algorithm_frequency
- Parallel implementations
- Benchmarking
"""

import unittest
import sys
import os
import math

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.constants import (
    OMEGA_CRITICAL,
    KAPPA_PI,
    spectral_sweep_analysis,
    monte_carlo_validation,
    optimize_algorithm_frequency,
)


class TestSpectralSweepAnalysis(unittest.TestCase):
    """Test spectral sweep analysis functionality."""
    
    def test_spectral_sweep_basic(self):
        """Test basic spectral sweep functionality."""
        frequencies = [0.0, 50.0, 100.0, OMEGA_CRITICAL, 200.0]
        results = spectral_sweep_analysis(100, 50, frequencies)
        
        # Should return one result per frequency
        self.assertEqual(len(results), len(frequencies))
        
        # Each result should have expected keys
        for result in results:
            self.assertIn('frequency_omega', result)
            self.assertIn('kappa_at_frequency', result)
            self.assertIn('time_ic_bits', result)
    
    def test_spectral_sweep_ordering(self):
        """Test that results correspond to input frequencies."""
        frequencies = [0.0, OMEGA_CRITICAL]
        results = spectral_sweep_analysis(100, 50, frequencies)
        
        # Classical frequency should have larger kappa
        self.assertGreater(results[0]['kappa_at_frequency'], 
                          results[1]['kappa_at_frequency'])
        
        # Critical frequency should have larger IC
        self.assertGreater(results[1]['time_ic_bits'], 
                          results[0]['time_ic_bits'])
    
    def test_spectral_sweep_single_frequency(self):
        """Test sweep with single frequency."""
        results = spectral_sweep_analysis(100, 50, [OMEGA_CRITICAL])
        
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0]['frequency_omega'], OMEGA_CRITICAL)


class TestMonteCarloValidation(unittest.TestCase):
    """Test Monte Carlo validation functionality."""
    
    def test_monte_carlo_basic(self):
        """Test basic Monte Carlo validation."""
        result = monte_carlo_validation(
            num_vars_range=(10, 50),
            n_samples=100,
            omega=0.0
        )
        
        # Check required fields
        self.assertIn('n_samples', result)
        self.assertIn('mean_predicted_ic', result)
        self.assertIn('std_predicted_ic', result)
        self.assertIn('statistical_error', result)
        self.assertIn('confidence_interval_95', result)
        self.assertIn('samples', result)
        
        # Check values are reasonable
        self.assertGreater(result['mean_predicted_ic'], 0)
        self.assertGreater(result['std_predicted_ic'], 0)
        self.assertGreater(result['statistical_error'], 0)
    
    def test_monte_carlo_sample_count(self):
        """Test that correct number of samples are generated."""
        n_samples = 50
        result = monte_carlo_validation(
            num_vars_range=(10, 50),
            n_samples=n_samples,
            omega=0.0
        )
        
        # Should generate samples for classical frequency only
        self.assertEqual(result['n_samples'], n_samples)
    
    def test_monte_carlo_both_frequencies(self):
        """Test Monte Carlo with both frequencies."""
        n_samples = 50
        result = monte_carlo_validation(
            num_vars_range=(10, 50),
            n_samples=n_samples,
            omega=None  # Both frequencies
        )
        
        # Should generate samples for both frequencies
        self.assertEqual(result['n_samples'], n_samples * 2)
        self.assertEqual(len(result['frequencies_tested']), 2)
    
    def test_monte_carlo_confidence_interval(self):
        """Test confidence interval calculation."""
        result = monte_carlo_validation(
            num_vars_range=(20, 30),
            n_samples=100,
            omega=0.0
        )
        
        ci_lower, ci_upper = result['confidence_interval_95']
        mean = result['mean_predicted_ic']
        
        # Confidence interval should contain mean
        self.assertLess(ci_lower, mean)
        self.assertGreater(ci_upper, mean)
        
        # Confidence interval should be symmetric around mean
        self.assertAlmostEqual(mean - ci_lower, ci_upper - mean, places=4)


class TestOptimizeAlgorithmFrequency(unittest.TestCase):
    """Test frequency optimization functionality."""
    
    def test_optimize_basic(self):
        """Test basic frequency optimization."""
        result = optimize_algorithm_frequency(
            num_vars=100,
            treewidth=50,
            frequency_range=(0.0, 200.0),
            num_points=20
        )
        
        # Check required fields
        self.assertIn('optimal_frequency', result)
        self.assertIn('min_ic_frequency', result)
        self.assertIn('max_ic_frequency', result)
        self.assertIn('critical_frequency', result)
        self.assertIn('sweep_data', result)
        
        # Check sweep data
        self.assertEqual(len(result['sweep_data']), 20)
    
    def test_optimize_frequency_range(self):
        """Test that optimal frequency is within range."""
        freq_min = 0.0
        freq_max = 200.0
        
        result = optimize_algorithm_frequency(
            num_vars=100,
            treewidth=50,
            frequency_range=(freq_min, freq_max),
            num_points=20
        )
        
        # Optimal frequency should be in range
        self.assertGreaterEqual(result['optimal_frequency'], freq_min)
        self.assertLessEqual(result['optimal_frequency'], freq_max)
        
        # Min and max IC frequencies should be in range
        self.assertGreaterEqual(result['min_ic_frequency'], freq_min)
        self.assertLessEqual(result['min_ic_frequency'], freq_max)
        self.assertGreaterEqual(result['max_ic_frequency'], freq_min)
        self.assertLessEqual(result['max_ic_frequency'], freq_max)
    
    def test_optimize_min_max_relationship(self):
        """Test relationship between min and max IC."""
        result = optimize_algorithm_frequency(
            num_vars=100,
            treewidth=50,
            frequency_range=(0.0, 200.0),
            num_points=30
        )
        
        # Max IC value should be greater than min IC value
        self.assertGreater(result['max_ic_value'], result['min_ic_value'])
    
    def test_optimize_critical_frequency_identified(self):
        """Test that critical frequency is correctly identified."""
        result = optimize_algorithm_frequency(
            num_vars=100,
            treewidth=50,
            frequency_range=(0.0, 200.0),
            num_points=50
        )
        
        # Critical frequency should be OMEGA_CRITICAL
        self.assertEqual(result['critical_frequency'], OMEGA_CRITICAL)


class TestExtensionIntegration(unittest.TestCase):
    """Test integration between different extension modules."""
    
    def test_sweep_to_optimization(self):
        """Test using sweep results in optimization."""
        # First do a sweep
        frequencies = [0.0, 50.0, 100.0, OMEGA_CRITICAL, 150.0, 200.0]
        sweep_results = spectral_sweep_analysis(100, 50, frequencies)
        
        # Find min IC from sweep
        min_ic_sweep = min(r['time_ic_bits'] for r in sweep_results)
        
        # Now do optimization
        opt_result = optimize_algorithm_frequency(100, 50, num_points=20)
        
        # Optimization should find similar or better minimum
        # (may not be exact due to different sampling)
        self.assertLessEqual(opt_result['min_ic_value'], min_ic_sweep * 1.5)
    
    def test_monte_carlo_consistency(self):
        """Test Monte Carlo consistency across runs."""
        # Run twice with same parameters
        result1 = monte_carlo_validation(
            num_vars_range=(20, 30),
            n_samples=200,
            omega=0.0
        )
        
        result2 = monte_carlo_validation(
            num_vars_range=(20, 30),
            n_samples=200,
            omega=0.0
        )
        
        # Means should be similar (within 2 standard errors)
        mean_diff = abs(result1['mean_predicted_ic'] - result2['mean_predicted_ic'])
        combined_error = result1['statistical_error'] + result2['statistical_error']
        
        self.assertLess(mean_diff, 2 * combined_error)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions."""
    
    def test_spectral_sweep_empty_frequencies(self):
        """Test sweep with empty frequency list."""
        results = spectral_sweep_analysis(100, 50, [])
        self.assertEqual(len(results), 0)
    
    def test_monte_carlo_small_sample(self):
        """Test Monte Carlo with very small sample size."""
        result = monte_carlo_validation(
            num_vars_range=(10, 20),
            n_samples=5,
            omega=0.0
        )
        
        # Should still return valid results
        self.assertGreater(result['mean_predicted_ic'], 0)
    
    def test_optimize_single_point(self):
        """Test optimization with single frequency point."""
        result = optimize_algorithm_frequency(100, 50, num_points=1)
        
        # Should still work, but all frequencies are the same
        self.assertEqual(result['min_ic_frequency'], result['max_ic_frequency'])
    
    def test_small_problem_sizes(self):
        """Test with very small problem sizes."""
        # Small n
        result = monte_carlo_validation(
            num_vars_range=(2, 5),
            n_samples=10,
            omega=0.0
        )
        
        self.assertGreater(result['mean_predicted_ic'], 0)
        
        # Small frequencies
        sweep = spectral_sweep_analysis(5, 2, [0.0, 1.0, 2.0])
        self.assertEqual(len(sweep), 3)


if __name__ == '__main__':
    print("=" * 70)
    print("Testing Advanced Frequency Dimension Extensions")
    print("=" * 70)
    print()
    
    # Run tests
    unittest.main(verbosity=2)
