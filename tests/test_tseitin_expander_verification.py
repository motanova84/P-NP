"""
Unit tests for Tseitin expander verification implementation

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from tseitin_expander_verification import (
    next_prime,
    is_prime,
    expander_degree,
    expander_shifts,
    construct_circulant_expander,
    xor_clauses,
    tseitin_encoding,
    tseitin_expander_formula,
    count_vars,
    verify_regularity,
    estimate_treewidth_lower_bound,
    BoolVar,
    Literal
)


class TestPrimalityFunctions(unittest.TestCase):
    """Test cases for primality helper functions."""
    
    def test_is_prime(self):
        """Test prime checking function."""
        self.assertTrue(is_prime(2))
        self.assertTrue(is_prime(3))
        self.assertTrue(is_prime(5))
        self.assertTrue(is_prime(7))
        self.assertTrue(is_prime(11))
        
        self.assertFalse(is_prime(0))
        self.assertFalse(is_prime(1))
        self.assertFalse(is_prime(4))
        self.assertFalse(is_prime(6))
        self.assertFalse(is_prime(9))
    
    def test_next_prime(self):
        """Test next prime function."""
        self.assertEqual(next_prime(1), 2)
        self.assertEqual(next_prime(2), 2)
        self.assertEqual(next_prime(3), 3)
        self.assertEqual(next_prime(4), 5)
        self.assertEqual(next_prime(10), 11)


class TestExpanderConstruction(unittest.TestCase):
    """Test cases for expander graph construction."""
    
    def test_expander_degree(self):
        """Test degree selection for expanders."""
        # For even n, should get odd degree
        d = expander_degree(10)
        self.assertEqual(d % 2, 1, "Degree should be odd for even n")
        
        d = expander_degree(14)
        self.assertEqual(d % 2, 1, "Degree should be odd for even n")
    
    def test_construct_circulant_expander(self):
        """Test circulant expander construction."""
        n = 10
        G = construct_circulant_expander(n)
        
        # Verify basic properties
        self.assertEqual(len(G), n, "Graph should have n vertices")
        
        # Verify regularity
        is_regular, d = verify_regularity(G)
        self.assertTrue(is_regular, "Graph should be d-regular")
        self.assertGreater(d, 0, "Degree should be positive")
    
    def test_regularity_verification(self):
        """Test verify_regularity function."""
        n = 14
        G = construct_circulant_expander(n)
        
        is_regular, d = verify_regularity(G)
        self.assertTrue(is_regular, "Circulant graph should be regular")
        
        # All nodes should have the same degree
        degrees = [G.degree(v) for v in G.nodes()]
        self.assertEqual(len(set(degrees)), 1, "All degrees should be equal")
        self.assertEqual(degrees[0], d, "Degree should match verify_regularity output")


class TestTseitinEncoding(unittest.TestCase):
    """Test cases for Tseitin encoding."""
    
    def test_xor_clauses_basic(self):
        """Test XOR clause generation for small cases."""
        # Single variable: XOR = 1 means variable must be true
        vars = [BoolVar(1)]
        clauses = xor_clauses(vars)
        self.assertGreater(len(clauses), 0, "Should generate clauses")
    
    def test_tseitin_encoding_small(self):
        """Test Tseitin encoding on small graph."""
        import networkx as nx
        
        # Triangle graph
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (2, 0)])
        
        formula = tseitin_encoding(G)
        self.assertGreater(len(formula), 0, "Should generate formula")
        
        # Should have variables for edges
        num_vars = count_vars(formula)
        self.assertEqual(num_vars, 3, "Triangle has 3 edges")
    
    def test_tseitin_expander_formula(self):
        """Test main Tseitin expander formula construction."""
        n = 10
        formula = tseitin_expander_formula(n)
        
        self.assertGreater(len(formula), 0, "Should generate formula")
        
        # Verify we have variables
        num_vars = count_vars(formula)
        self.assertGreater(num_vars, 0, "Should have variables")


class TestAnalysisFunctions(unittest.TestCase):
    """Test cases for analysis functions."""
    
    def test_count_vars(self):
        """Test variable counting."""
        # Create simple formula
        formula = [
            [Literal(BoolVar(1), False), Literal(BoolVar(2), True)],
            [Literal(BoolVar(2), False), Literal(BoolVar(3), True)],
        ]
        
        num_vars = count_vars(formula)
        self.assertEqual(num_vars, 3, "Should count 3 distinct variables")
    
    def test_estimate_treewidth_lower_bound(self):
        """Test treewidth estimation."""
        import networkx as nx
        
        # Create a small graph
        G = nx.circulant_graph(10, [1, 5])
        
        tw_lower = estimate_treewidth_lower_bound(G)
        self.assertGreater(tw_lower, 0, "Treewidth lower bound should be positive")


class TestIntegration(unittest.TestCase):
    """Integration tests for complete workflow."""
    
    def test_full_construction_workflow(self):
        """Test complete construction workflow for a small instance."""
        n = 14
        
        # Build graph
        G = construct_circulant_expander(n)
        
        # Verify regularity
        is_regular, d = verify_regularity(G)
        self.assertTrue(is_regular, "Graph should be regular")
        
        # For even n, degree should be odd
        self.assertEqual(d % 2, 1, "Degree should be odd for even n")
        
        # Generate Tseitin formula
        formula = tseitin_expander_formula(n)
        self.assertGreater(len(formula), 0, "Should generate formula")
        
        # Count variables
        num_vars = count_vars(formula)
        self.assertEqual(num_vars, G.number_of_edges(), 
                        "Should have one variable per edge")
        
        # Estimate treewidth
        tw_lower = estimate_treewidth_lower_bound(G)
        self.assertGreater(tw_lower, 0, "Should have positive treewidth")


if __name__ == '__main__':
    print("Running Tseitin Expander Verification Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
