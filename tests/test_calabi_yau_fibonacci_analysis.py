#!/usr/bin/env python3
"""
test_calabi_yau_fibonacci_analysis.py - Tests for Fibonacci structure analysis

Tests for the Fibonacci structure investigation in Calabi-Yau moduli spaces.

© JMMB | P vs NP Verification System
"""

import unittest
import sys
import os
import math
import pandas as pd
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_fibonacci_analysis import (
    fibonacci_sequence,
    phi_power_sequence,
    verify_phi_fibonacci_relation,
    load_extended_cy_data,
    compute_fibonacci_metrics,
    analyze_phi_squared_clustering,
    test_fibonacci_recursion_hypothesis,
    PHI,
    PHI_SQUARED,
    KAPPA_PI_TARGET
)


class TestFibonacciSequence(unittest.TestCase):
    """Test Fibonacci sequence generation."""
    
    def test_fibonacci_basic(self):
        """Test basic Fibonacci sequence."""
        fib = fibonacci_sequence(10)
        expected = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
        self.assertEqual(fib, expected)
    
    def test_fibonacci_edge_cases(self):
        """Test edge cases for Fibonacci sequence."""
        self.assertEqual(fibonacci_sequence(0), [0])
        self.assertEqual(fibonacci_sequence(1), [0, 1])
        self.assertEqual(fibonacci_sequence(-1), [])
    
    def test_fibonacci_properties(self):
        """Test Fibonacci sequence properties."""
        fib = fibonacci_sequence(20)
        # Each number is sum of previous two
        for i in range(2, len(fib)):
            self.assertEqual(fib[i], fib[i-1] + fib[i-2])


class TestPhiPowers(unittest.TestCase):
    """Test φ^n sequence generation."""
    
    def test_phi_powers_basic(self):
        """Test basic φ^n generation."""
        phi_powers = phi_power_sequence(5)
        self.assertEqual(len(phi_powers), 5)
        
        # Check first few values
        self.assertAlmostEqual(phi_powers[0], PHI, places=10)
        self.assertAlmostEqual(phi_powers[1], PHI ** 2, places=10)
        self.assertAlmostEqual(phi_powers[2], PHI ** 3, places=10)
    
    def test_phi_squared_value(self):
        """Test that φ² = φ + 1."""
        phi_sq = PHI ** 2
        expected = PHI + 1
        self.assertAlmostEqual(phi_sq, expected, places=10)
        self.assertAlmostEqual(PHI_SQUARED, expected, places=10)


class TestPhiFibonacciRelation(unittest.TestCase):
    """Test the relation between φ^n and Fibonacci numbers."""
    
    def test_phi_fibonacci_relation(self):
        """Test φ^n = F_n·φ + F_{n-1}."""
        for n in range(1, 15):
            result = verify_phi_fibonacci_relation(n)
            self.assertTrue(result['verified'], 
                          f"Failed for n={n}: difference={result['difference']}")
    
    def test_relation_accuracy(self):
        """Test numerical accuracy of the relation."""
        result = verify_phi_fibonacci_relation(10)
        self.assertLess(result['difference'], 1e-10)


class TestCalabiYauData(unittest.TestCase):
    """Test Calabi-Yau data loading and processing."""
    
    def test_load_data(self):
        """Test loading of extended CY data."""
        df = load_extended_cy_data()
        
        # Should have data
        self.assertGreater(len(df), 0)
        
        # Should have required columns
        required_cols = ['name', 'h11', 'h21', 'reference']
        for col in required_cols:
            self.assertIn(col, df.columns)
    
    def test_data_validity(self):
        """Test that loaded data is valid."""
        df = load_extended_cy_data()
        
        # Hodge numbers should be non-negative
        self.assertTrue((df['h11'] >= 0).all())
        self.assertTrue((df['h21'] >= 0).all())
        
        # At least one should be positive for each variety
        self.assertTrue(((df['h11'] > 0) | (df['h21'] > 0)).all())
    
    def test_fibonacci_number_varieties(self):
        """Test that we have varieties with N = Fibonacci numbers."""
        df = load_extended_cy_data()
        df['N'] = df['h11'] + df['h21']
        
        # Should have varieties with Fibonacci N values
        fib_nums = [2, 3, 5, 8, 13, 21]
        for fib in fib_nums:
            varieties_at_fib = df[df['N'] == fib]
            self.assertGreater(len(varieties_at_fib), 0,
                             f"No varieties found with N = {fib}")


class TestFibonacciMetrics(unittest.TestCase):
    """Test Fibonacci metric computation."""
    
    def setUp(self):
        """Set up test data."""
        self.df = load_extended_cy_data()
        self.df_metrics = compute_fibonacci_metrics(self.df)
    
    def test_basic_metrics(self):
        """Test basic metric computation."""
        # Should have N column
        self.assertIn('N', self.df_metrics.columns)
        self.assertTrue((self.df_metrics['N'] == 
                        self.df_metrics['h11'] + self.df_metrics['h21']).all())
    
    def test_fibonacci_detection(self):
        """Test Fibonacci number detection."""
        self.assertIn('is_fibonacci', self.df_metrics.columns)
        self.assertIn('closest_fib', self.df_metrics.columns)
        
        # Varieties with N = Fibonacci should be marked
        fib_varieties = self.df_metrics[self.df_metrics['is_fibonacci']]
        self.assertGreater(len(fib_varieties), 0)
        
        # Their distance to Fibonacci should be 0
        self.assertTrue((fib_varieties['dist_to_fib'] == 0).all())
    
    def test_phi_n_metrics(self):
        """Test φ^n related metrics."""
        required_cols = ['closest_phi_n', 'closest_phi_n_value', 'dist_to_phi_n']
        for col in required_cols:
            self.assertIn(col, self.df_metrics.columns)
    
    def test_kappa_phi2_computation(self):
        """Test κ_Π computation with base φ²."""
        self.assertIn('kappa_phi2', self.df_metrics.columns)
        
        # κ_Π should be positive for N > 1
        varieties_N_gt_1 = self.df_metrics[self.df_metrics['N'] > 1]
        self.assertTrue((varieties_N_gt_1['kappa_phi2'] > 0).all())
        
        # Verify computation for a specific case
        N13_varieties = self.df_metrics[self.df_metrics['N'] == 13]
        if len(N13_varieties) > 0:
            expected_kappa = math.log(13) / math.log(PHI_SQUARED)
            actual_kappa = N13_varieties.iloc[0]['kappa_phi2']
            self.assertAlmostEqual(actual_kappa, expected_kappa, places=10)


class TestPhiSquaredClustering(unittest.TestCase):
    """Test clustering analysis near φ²."""
    
    def setUp(self):
        """Set up test data."""
        df = load_extended_cy_data()
        self.df_metrics = compute_fibonacci_metrics(df)
    
    def test_clustering_analysis(self):
        """Test basic clustering analysis."""
        result = analyze_phi_squared_clustering(self.df_metrics)
        
        # Should have expected keys
        required_keys = ['total_ratios', 'mean_ratio', 'median_ratio',
                        'close_to_phi_count', 'close_to_phi2_count',
                        'clustering_evidence']
        for key in required_keys:
            self.assertIn(key, result)
    
    def test_ratio_statistics(self):
        """Test ratio statistics are reasonable."""
        result = analyze_phi_squared_clustering(self.df_metrics)
        
        # Mean and median should be positive
        self.assertGreater(result['mean_ratio'], 0)
        self.assertGreater(result['median_ratio'], 0)
        
        # Standard deviation should be non-negative
        self.assertGreaterEqual(result['std_ratio'], 0)
    
    def test_phi_constants(self):
        """Test that φ constants are correctly stored."""
        result = analyze_phi_squared_clustering(self.df_metrics)
        
        self.assertAlmostEqual(result['phi'], PHI, places=10)
        self.assertAlmostEqual(result['phi_squared'], PHI_SQUARED, places=10)


class TestFibonacciRecursion(unittest.TestCase):
    """Test Fibonacci recursion hypothesis."""
    
    def setUp(self):
        """Set up test data."""
        self.df = load_extended_cy_data()
    
    def test_recursion_test(self):
        """Test recursion hypothesis test."""
        result = test_fibonacci_recursion_hypothesis(self.df)
        
        # Should have expected keys
        required_keys = ['total_tested', 'fibonacci_like_count', 
                        'fibonacci_percentage', 'details']
        for key in required_keys:
            self.assertIn(key, result)
    
    def test_recursion_percentage(self):
        """Test that recursion percentage is valid."""
        result = test_fibonacci_recursion_hypothesis(self.df)
        
        # Percentage should be between 0 and 100
        self.assertGreaterEqual(result['fibonacci_percentage'], 0)
        self.assertLessEqual(result['fibonacci_percentage'], 100)
    
    def test_recursion_details(self):
        """Test that recursion details are properly structured."""
        result = test_fibonacci_recursion_hypothesis(self.df)
        
        if result['total_tested'] > 0:
            # Each detail should have required fields
            detail = result['details'][0]
            required_fields = ['N_curr', 'N_prev1', 'N_prev2', 
                             'expected_sum', 'deviation', 'is_fibonacci_like']
            for field in required_fields:
                self.assertIn(field, detail)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete analysis."""
    
    def test_complete_pipeline(self):
        """Test that complete analysis pipeline runs."""
        # Load data
        df = load_extended_cy_data()
        
        # Compute metrics
        df = compute_fibonacci_metrics(df)
        
        # Run analyses
        clustering = analyze_phi_squared_clustering(df)
        recursion = test_fibonacci_recursion_hypothesis(df)
        
        # All should succeed
        self.assertIsNotNone(clustering)
        self.assertIsNotNone(recursion)
    
    def test_n13_special_case(self):
        """Test special case of N=13 varieties."""
        df = load_extended_cy_data()
        df = compute_fibonacci_metrics(df)
        
        # Should have N=13 varieties
        n13 = df[df['N'] == 13]
        self.assertGreater(len(n13), 0)
        
        # Their κ_Π should be close to target
        kappa_mean = n13['kappa_phi2'].mean()
        # Allow some deviation but should be in same ballpark
        self.assertLess(abs(kappa_mean - KAPPA_PI_TARGET), 0.2)


def run_tests():
    """Run all tests."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
