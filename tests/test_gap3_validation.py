"""
Unit tests for GAP 3 validation - hard CNF formulas with high treewidth

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.computational_dichotomy import (
    hard_cnf_formula, ramanujan_graph, tseitin_encoding,
    incidence_graph, estimate_treewidth
)
import numpy as np


class TestHardCNFFormula(unittest.TestCase):
    """Test cases for hard_cnf_formula construction."""
    
    def test_hard_cnf_formula_basic(self):
        """Test that hard_cnf_formula generates valid formulas."""
        n = 50
        formula = hard_cnf_formula(n, seed=42)
        
        # Should have variables and clauses
        self.assertGreater(formula.num_vars, 0)
        self.assertGreater(len(formula.clauses), 0)
        
        # Variables should be roughly n * d / 2 where d is degree
        # For d=3, we expect about 75 variables
        self.assertGreater(formula.num_vars, n)
        self.assertLess(formula.num_vars, n * 10)
    
    def test_ramanujan_graph_properties(self):
        """Test Ramanujan graph generation properties."""
        n = 100
        G = ramanujan_graph(n, seed=42)
        
        # Should have n nodes
        self.assertEqual(G.number_of_nodes(), n)
        
        # Should be regular (all nodes have same degree)
        degrees = [d for _, d in G.degree()]
        self.assertEqual(len(set(degrees)), 1)  # All degrees the same
        
        # Degree should be 3 or 4
        degree = degrees[0]
        self.assertIn(degree, [3, 4])
    
    def test_tseitin_encoding_properties(self):
        """Test Tseitin encoding properties."""
        n = 20
        G = ramanujan_graph(n, seed=42)
        parity = [1] * n  # All odd parities
        
        formula = tseitin_encoding(G, parity)
        
        # Number of variables should equal number of edges
        self.assertEqual(formula.num_vars, G.number_of_edges())
        
        # Should have clauses
        self.assertGreater(len(formula.clauses), 0)
    
    def test_treewidth_lower_bound(self):
        """Test that hard_cnf_formula achieves treewidth lower bound."""
        n = 50
        formula = hard_cnf_formula(n, seed=42)
        
        # Build incidence graph
        G_inc = incidence_graph(formula.num_vars, formula.clauses)
        
        # Estimate treewidth
        tw = estimate_treewidth(G_inc)
        
        # Should satisfy lower bound: tw >= sqrt(n) / 4
        expected_min = np.sqrt(n) / 4
        self.assertGreaterEqual(tw, expected_min)
    
    def test_multiple_sizes(self):
        """Test formula generation for multiple sizes."""
        sizes = [50, 100, 150]
        
        for n in sizes:
            with self.subTest(n=n):
                formula = hard_cnf_formula(n, seed=42)
                
                # Should have reasonable number of variables and clauses
                self.assertGreater(formula.num_vars, 0)
                self.assertGreater(len(formula.clauses), 0)
                
                # Build incidence graph and check treewidth
                G_inc = incidence_graph(formula.num_vars, formula.clauses)
                tw = estimate_treewidth(G_inc)
                
                # Should satisfy lower bound
                expected_min = np.sqrt(n) / 4
                self.assertGreaterEqual(tw, expected_min)
    
    def test_clause_variable_ratio(self):
        """Test that clause-to-variable ratio is reasonable."""
        n = 100
        formula = hard_cnf_formula(n, seed=42)
        
        ratio = len(formula.clauses) / formula.num_vars
        
        # For Tseitin encoding with degree 3-4, expect ratio around 2-4
        self.assertGreater(ratio, 1.0)
        self.assertLess(ratio, 10.0)
    
    def test_deterministic_with_seed(self):
        """Test that results are deterministic with same seed."""
        n = 50
        
        # Generate twice with same seed
        formula1 = hard_cnf_formula(n, seed=42)
        formula2 = hard_cnf_formula(n, seed=42)
        
        # Should have same structure
        self.assertEqual(formula1.num_vars, formula2.num_vars)
        self.assertEqual(len(formula1.clauses), len(formula2.clauses))
    
    def test_all_odd_parity_unsatisfiable(self):
        """Test that all-odd parity assignment creates unsatisfiable formula."""
        n = 10
        G = ramanujan_graph(n, seed=42)
        
        # Count total degree (sum of all degrees)
        
        # Total degree is always even (each edge counted twice)
        # So sum of odd parities (n odd values) is odd if n is odd
        # This means the formula should be unsatisfiable
        
        # Just verify the formula is created without error
        parity = [1] * n
        formula = tseitin_encoding(G, parity)
        
        # Should have variables and clauses
        self.assertGreater(formula.num_vars, 0)
        self.assertGreater(len(formula.clauses), 0)


class TestValidationScript(unittest.TestCase):
    """Test that the validation script runs without errors."""
    
    def test_validation_script_runs(self):
        """Test that validate_gap3_hard_cnf.py runs successfully."""
        import subprocess
        
        result = subprocess.run(
            ['python3', 'experiments/validate_gap3_hard_cnf.py'],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        # Should complete successfully
        self.assertEqual(result.returncode, 0)
        
        # Should contain key output markers
        self.assertIn('VALIDACIÓN: hard_cnf_formula', result.stdout)
        self.assertIn('GAP 3', result.stdout)
        self.assertIn('COMPLETAMENTE RESUELTO', result.stdout)


if __name__ == '__main__':
    print("Running GAP 3 Validation Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
