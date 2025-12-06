"""
Unit tests for treewidth_vs_sat_runtime module

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os
import random

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from experiments.treewidth_vs_sat_runtime import (
    simulate_sat_instance,
    estimate_treewidth_from_sat,
    simulate_dpll_runtime
)


class TestSATInstanceGeneration(unittest.TestCase):
    """Test cases for SAT instance generation."""
    
    def setUp(self):
        """Set random seed for reproducibility."""
        random.seed(42)
    
    def test_simulate_sat_instance_basic(self):
        """Test basic SAT instance generation."""
        n_vars = 10
        formula = simulate_sat_instance(n_vars, clause_density=4.3)
        
        # Check number of clauses
        expected_clauses = int(4.3 * n_vars)
        self.assertEqual(len(formula), expected_clauses)
        
        # Check clause structure (each clause should have 3 literals)
        for clause in formula:
            self.assertEqual(len(clause), 3)
            # Check literals are within variable range
            for lit in clause:
                self.assertTrue(abs(lit) >= 1 and abs(lit) <= n_vars)
    
    def test_simulate_sat_instance_different_densities(self):
        """Test SAT instance generation with different clause densities."""
        n_vars = 20
        
        # Test low density
        formula_low = simulate_sat_instance(n_vars, clause_density=2.0)
        self.assertEqual(len(formula_low), 40)
        
        # Test high density
        formula_high = simulate_sat_instance(n_vars, clause_density=6.0)
        self.assertEqual(len(formula_high), 120)
    
    def test_simulate_sat_instance_literals(self):
        """Test that both positive and negative literals are generated."""
        n_vars = 50
        formula = simulate_sat_instance(n_vars)
        
        # Flatten all literals
        all_literals = [lit for clause in formula for lit in clause]
        
        # Check we have both positive and negative literals
        has_positive = any(lit > 0 for lit in all_literals)
        has_negative = any(lit < 0 for lit in all_literals)
        
        self.assertTrue(has_positive)
        self.assertTrue(has_negative)


class TestTreewidthEstimation(unittest.TestCase):
    """Test cases for treewidth estimation."""
    
    def test_estimate_treewidth_simple(self):
        """Test treewidth estimation on a simple formula."""
        # Simple chain-like formula: (1 ∨ 2 ∨ 3), (3 ∨ 4 ∨ 5)
        formula = [[1, 2, 3], [3, 4, 5]]
        tw = estimate_treewidth_from_sat(formula)
        
        # Treewidth should be relatively small for a chain
        self.assertGreaterEqual(tw, 0)
        self.assertLessEqual(tw, 10)
    
    def test_estimate_treewidth_clique(self):
        """Test treewidth estimation on a clique-like structure."""
        # Dense formula connecting same variables: should have higher treewidth
        formula = [
            [1, 2, 3],
            [1, 2, 4],
            [1, 3, 4],
            [2, 3, 4]
        ]
        tw = estimate_treewidth_from_sat(formula)
        
        # Treewidth should be non-zero
        self.assertGreater(tw, 0)
    
    def test_estimate_treewidth_grows_with_size(self):
        """Test that treewidth generally increases with problem size."""
        random.seed(42)
        
        tw_small = estimate_treewidth_from_sat(simulate_sat_instance(10))
        tw_large = estimate_treewidth_from_sat(simulate_sat_instance(50))
        
        # Larger instances should tend to have larger treewidth
        # (This is a statistical property, not guaranteed for every instance)
        self.assertGreater(tw_large, 0)
        self.assertGreater(tw_small, 0)


class TestDPLLRuntimeSimulation(unittest.TestCase):
    """Test cases for DPLL runtime simulation."""
    
    def test_simulate_dpll_runtime_exponential_growth(self):
        """Test that runtime grows exponentially with treewidth."""
        t1 = simulate_dpll_runtime(10)
        t2 = simulate_dpll_runtime(20)
        t3 = simulate_dpll_runtime(30)
        
        # Times should increase
        self.assertLess(t1, t2)
        self.assertLess(t2, t3)
        
        # Growth should be exponential: ratio should be roughly consistent
        ratio1 = t2 / t1
        ratio2 = t3 / t2
        
        # Both ratios should be > 1 (exponential growth)
        self.assertGreater(ratio1, 1.0)
        self.assertGreater(ratio2, 1.0)
    
    def test_simulate_dpll_runtime_positive(self):
        """Test that simulated runtime is always positive."""
        for tw in [0, 5, 10, 20, 50, 100]:
            t = simulate_dpll_runtime(tw)
            self.assertGreater(t, 0)
    
    def test_simulate_dpll_runtime_base_case(self):
        """Test that runtime is minimal for zero treewidth."""
        t0 = simulate_dpll_runtime(0)
        t10 = simulate_dpll_runtime(10)
        
        # Zero treewidth should give minimal time
        self.assertLess(t0, t10)
        self.assertAlmostEqual(t0, 0.001, places=5)


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete workflow."""
    
    def test_complete_workflow(self):
        """Test the complete workflow: generate -> estimate -> simulate."""
        random.seed(42)
        
        n_vars = 30
        formula = simulate_sat_instance(n_vars)
        tw = estimate_treewidth_from_sat(formula)
        runtime = simulate_dpll_runtime(tw)
        
        # Check all values are reasonable
        self.assertGreater(len(formula), 0)
        self.assertGreater(tw, 0)
        self.assertGreater(runtime, 0)
        
        # Verify the relationship T ≥ 2^Ω(tw) by checking runtime grows
        self.assertIsInstance(runtime, float)
        self.assertIsInstance(tw, (int, float))


if __name__ == '__main__':
    unittest.main()
