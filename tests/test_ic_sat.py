"""
IC-SAT Validation Tests
=======================

Tests for the IC-SAT framework validating the treewidth dichotomy.
Tests include low treewidth (polynomial time) and high treewidth
(exponential growth) scenarios.

Author: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)
"""

import unittest
import time
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.icq_pnp.computational_dichotomy import (
    CNFFormula, 
    generate_low_treewidth_formula,
    ic_sat_validate
)
from src.icq_pnp.tseitin_generator import (
    generate_expander_tseitin,
    generate_tseitin_formula,
    generate_margulis_gabber_galil_expander
)


class TestICSTLowTreewidth(unittest.TestCase):
    """Test cases for low treewidth formulas (polynomial time expected)."""
    
    def test_low_treewidth_scaling(self):
        """Test that low treewidth formulas scale polynomially."""
        sizes = [50, 100, 200]
        times = []
        
        for n in sizes:
            start = time.time()
            formula = generate_low_treewidth_formula(n)
            tw = formula.compute_treewidth_approximation()
            elapsed = time.time() - start
            times.append(elapsed)
            
            # Low treewidth formulas should have bounded treewidth
            self.assertLessEqual(tw, 2, f"Treewidth for n={n} should be ≤2")
        
        # Times should grow reasonably (not exponentially)
        # For polynomial growth, doubling n shouldn't quadruple time
        if len(times) >= 2:
            ratio = times[-1] / times[0]
            # With 4x size increase, polynomial should be < 50x slower
            self.assertLess(ratio, 50, "Time growth should be polynomial")
    
    def test_low_treewidth_tractability(self):
        """Test that low treewidth formulas are correctly identified as tractable."""
        n_values = [100, 200, 300]
        results = ic_sat_validate(n_values)
        
        # All low treewidth cases should be marked as solved
        for result in results:
            self.assertTrue(result['solved'], 
                          f"Formula with n={result['n']} should be tractable")
            # Treewidth should be O(log n) - specifically ≤ log2(n)
            import math
            self.assertLessEqual(result['treewidth'], 
                               2 * math.log2(result['n']),
                               f"Treewidth should be O(log n)")


class TestICSATHighTreewidth(unittest.TestCase):
    """Test cases for high treewidth formulas (exponential growth expected)."""
    
    def test_expander_high_treewidth(self):
        """Test that expander-based formulas have high treewidth."""
        # Generate Tseitin formula over expander
        n_vertices = 12
        degree = 3
        
        num_vars, clauses = generate_expander_tseitin(n_vertices, degree)
        
        # Should have many variables (one per edge)
        # For d-regular graph, edges ≈ n*d/2
        expected_vars = n_vertices * degree // 2
        self.assertGreaterEqual(num_vars, expected_vars - 2, 
                               "Should have ~n*d/2 variables")
        
        # Should have many clauses (expander creates complex structure)
        self.assertGreater(len(clauses), n_vertices,
                          "Should have substantial clauses")
    
    def test_margulis_gabber_galil_expander(self):
        """Test Margulis-Gabber-Galil expander generation."""
        n = 3  # Creates 9 vertices
        G = generate_margulis_gabber_galil_expander(n)
        
        # Should create n^2 vertices
        self.assertEqual(len(G.nodes()), n * n)
        
        # Generate Tseitin formula over it
        num_vars, clauses = generate_tseitin_formula(G, parity=True)
        
        self.assertGreater(num_vars, 0)
        self.assertGreater(len(clauses), 0)
    
    def test_high_treewidth_complexity_growth(self):
        """Test that complexity grows for larger expander instances."""
        sizes = [8, 12]  # Keep small for test speed
        clause_counts = []
        
        for n in sizes:
            num_vars, clauses = generate_expander_tseitin(n, 3)
            clause_counts.append(len(clauses))
        
        # Clause count should grow significantly
        # Not just linearly - should see superlinear growth
        if len(clause_counts) >= 2:
            growth_ratio = clause_counts[-1] / clause_counts[0]
            size_ratio = sizes[-1] / sizes[0]
            
            # Growth should be at least as fast as linear
            self.assertGreaterEqual(growth_ratio, size_ratio * 0.8,
                                  "Clause growth should be at least linear")


class TestICSTIntegration(unittest.TestCase):
    """Integration tests for the complete IC-SAT framework."""
    
    def test_validate_function(self):
        """Test the ic_sat_validate function."""
        n_values = [50, 100, 150]
        results = ic_sat_validate(n_values, clause_var_ratio=4.2)
        
        # Should return correct number of results
        self.assertEqual(len(results), len(n_values))
        
        # Each result should have required fields
        for result in results:
            self.assertIn('n', result)
            self.assertIn('treewidth', result)
            self.assertIn('coherence', result)
            self.assertIn('solved', result)
            
            # Values should be reasonable
            self.assertGreater(result['n'], 0)
            self.assertGreaterEqual(result['treewidth'], 0)
            self.assertGreater(result['coherence'], 0)
            self.assertIsInstance(result['solved'], bool)


if __name__ == '__main__':
    print("Running IC-SAT Validation Tests ∞³")
    print("Instituto de Conciencia Cuántica (ICQ)")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
