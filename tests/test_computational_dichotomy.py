"""
Unit tests for computational dichotomy framework

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.computational_dichotomy import (
    CNF, incidence_graph, primal_graph, estimate_treewidth,
    predict_advantages, simplify_clauses, solve_sat_simple,
    ic_sat, compare_treewidths, LargeScaleValidation
)


class TestHelperFunctions(unittest.TestCase):
    """Test cases for helper functions."""
    
    def test_incidence_graph(self):
        """Test incidence graph construction."""
        n_vars = 3
        clauses = [[1, 2], [-1, 3]]
        G = incidence_graph(n_vars, clauses)
        
        self.assertEqual(G.number_of_nodes(), 5)  # 3 vars + 2 clauses
        self.assertEqual(G.number_of_edges(), 4)  # 2 edges from clause 0, 2 from clause 1
    
    def test_primal_graph(self):
        """Test primal graph construction."""
        clauses = [[1, 2, 3], [-1, -2]]
        n_vars = 3
        G = primal_graph(clauses, n_vars)
        
        self.assertEqual(G.number_of_nodes(), 3)
        self.assertGreaterEqual(G.number_of_edges(), 3)  # At least edges from first clause
    
    def test_estimate_treewidth(self):
        """Test treewidth estimation."""
        import networkx as nx
        G = nx.cycle_graph(5)  # Treewidth should be 2
        tw = estimate_treewidth(G)
        self.assertGreaterEqual(tw, 1)
        self.assertLessEqual(tw, 3)
    
    def test_simplify_clauses(self):
        """Test clause simplification."""
        clauses = [[1, 2], [-1, 3], [1, -3]]
        
        # Assign v1 = 1 (satisfies clauses with lit 1)
        result = simplify_clauses(clauses, 'v1', 1)
        self.assertIsNotNone(result)
        self.assertEqual(len(result), 1)  # Only [-1, 3] becomes [3]
    
    def test_solve_sat_simple(self):
        """Test simple SAT solver."""
        clauses = [[1, 2], [-1, 3]]
        result = solve_sat_simple(clauses)
        self.assertEqual(result, "SAT")
        
        # Empty clause should be UNSAT
        clauses_unsat = [[]]
        result_unsat = solve_sat_simple(clauses_unsat)
        self.assertEqual(result_unsat, "UNSAT")


class TestICsat(unittest.TestCase):
    """Test cases for IC-SAT algorithm."""
    
    def test_ic_sat_simple(self):
        """Test IC-SAT on simple instance."""
        n_vars = 2
        clauses = [[1, 2], [-1, -2]]
        G = incidence_graph(n_vars, clauses)
        
        result = ic_sat(G, clauses, n_vars, max_depth=3)
        self.assertIn(result, ["SAT", "UNSAT", "UNKNOWN"])
    
    def test_compare_treewidths(self):
        """Test treewidth comparison."""
        clauses = [[1, 2], [-1, 3]]
        n_vars = 3
        
        tw_p, tw_i = compare_treewidths(clauses, n_vars)
        self.assertGreaterEqual(tw_p, 0)
        self.assertGreaterEqual(tw_i, 0)


class TestCNF(unittest.TestCase):
    """Test cases for CNF class."""
    
    def test_cnf_creation(self):
        """Test CNF creation."""
        variables = ["x1", "x2", "x3"]
        clauses = [[1, 2], [-1, 3]]
        cnf = CNF(variables, clauses)
        
        self.assertEqual(cnf.n_vars, 3)
        self.assertEqual(len(cnf.clauses), 2)


class TestLargeScaleValidation(unittest.TestCase):
    """Test cases for large-scale validation."""
    
    def test_generate_3sat_critical(self):
        """Test 3-SAT generation."""
        validator = LargeScaleValidation()
        cnf = validator.generate_3sat_critical(5, ratio=4.0)
        
        self.assertEqual(cnf.n_vars, 5)
        self.assertEqual(len(cnf.clauses), 20)  # 5 * 4.0
        
        # Check that all clauses have 3 literals
        for clause in cnf.clauses:
            self.assertEqual(len(clause), 3)
    
    def test_run_large_scale(self):
        """Test large-scale validation run."""
        validator = LargeScaleValidation()
        results = validator.run_large_scale(n_values=[5], ratios=[4.0])
        
        self.assertEqual(len(results), 1)
        self.assertIn("n=5_r=4.0", results)
        
        result = results["n=5_r=4.0"]
        self.assertIn("tw_estimated", result)
        self.assertIn("coherence_C", result)


if __name__ == '__main__':
    print("Running Computational Dichotomy Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
