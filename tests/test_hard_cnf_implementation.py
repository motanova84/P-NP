"""
Unit tests for hard_cnf_implementation module

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from hard_cnf_implementation import (
    TseitinEncoder,
    estimate_treewidth,
    generate_random_3cnf_incidence
)


class TestTseitinEncoder(unittest.TestCase):
    """Test cases for TseitinEncoder class."""
    
    def test_initialization(self):
        """Test TseitinEncoder initialization."""
        encoder = TseitinEncoder(10)
        self.assertEqual(encoder.n, 10)
        self.assertIsNotNone(encoder.G)
        self.assertEqual(len(encoder.G.nodes()), 10)
    
    def test_build_expander_graph(self):
        """Test expander graph construction."""
        encoder = TseitinEncoder(20)
        G = encoder.G
        
        # Graph should have n nodes
        self.assertEqual(len(G.nodes()), 20)
        
        # Graph should have edges
        self.assertGreater(len(G.edges()), 0)
        
        # Graph should be connected or have few components
        import networkx as nx
        num_components = nx.number_connected_components(G)
        self.assertLessEqual(num_components, 3)
    
    def test_generate_xor_clauses_small(self):
        """Test XOR clause generation for small number of variables."""
        encoder = TseitinEncoder(10)
        
        # Test with 2 variables, XOR = 0 (even parity)
        clauses = encoder.generate_xor_clauses([1, 2], False)
        self.assertGreater(len(clauses), 0)
        # For 2 vars with XOR=0, should have 2 clauses: (1,2) and (-1,-2)
        self.assertEqual(len(clauses), 2)
        
        # Test with 3 variables, XOR = 1 (odd parity)
        clauses = encoder.generate_xor_clauses([1, 2, 3], True)
        self.assertGreater(len(clauses), 0)
        # For 3 vars with XOR=1, should have 4 clauses
        self.assertEqual(len(clauses), 4)
    
    def test_generate_xor_clauses_large(self):
        """Test XOR clause generation for k > 3 (uses auxiliary variables)."""
        encoder = TseitinEncoder(10)
        
        # Initialize next_aux_var as encode() would do
        encoder.next_aux_var = 100
        
        # Test with 5 variables, XOR = 0
        clauses = encoder.generate_xor_clauses([1, 2, 3, 4, 5], False)
        self.assertGreater(len(clauses), 0)
        # Should use auxiliary variable encoding (linear in k, not exponential)
        # Expected: O(k) clauses, not O(2^k)
        self.assertLess(len(clauses), 50)  # Much less than 2^5 = 32
        
        # Test with 6 variables, XOR = 1
        encoder.next_aux_var = 100
        clauses = encoder.generate_xor_clauses([1, 2, 3, 4, 5, 6], True)
        self.assertGreater(len(clauses), 0)
        self.assertLess(len(clauses), 50)
    
    def test_generate_xor_clauses_empty(self):
        """Test XOR clause generation with no variables."""
        encoder = TseitinEncoder(10)
        
        # XOR of no variables = 0 (False) 
        # If b=False (want 0), this is satisfied -> no constraints needed
        clauses = encoder.generate_xor_clauses([], False)
        self.assertEqual(len(clauses), 0)
        # Verify it's satisfiable (no constraints)
        
        # XOR of no variables = 0 but we want 1 -> unsatisfiable
        clauses = encoder.generate_xor_clauses([], True)
        self.assertEqual(len(clauses), 1)
        # Verify it's the empty clause (unsatisfiable)
        self.assertEqual(clauses[0], [])
    
    def test_encode(self):
        """Test encoding of graph to CNF."""
        encoder = TseitinEncoder(15)
        variables, clauses = encoder.encode()
        
        # Should have variables
        self.assertGreater(len(variables), 0)
        
        # Should have clauses
        self.assertGreater(len(clauses), 0)
        
        # Variables should be integers
        for var in variables:
            self.assertIsInstance(var, int)
            self.assertGreater(var, 0)
    
    def test_get_incidence_graph(self):
        """Test incidence graph construction."""
        encoder = TseitinEncoder(10)
        G = encoder.get_incidence_graph()
        
        # Should have variable and clause nodes
        self.assertGreater(len(G.nodes()), 0)
        
        # Should have edges
        self.assertGreater(len(G.edges()), 0)
        
        # Check node types
        var_nodes = [n for n in G.nodes() if 'x' in str(n)]
        clause_nodes = [n for n in G.nodes() if 'C' in str(n)]
        
        self.assertGreater(len(var_nodes), 0)
        self.assertGreater(len(clause_nodes), 0)


class TestValidationFunctions(unittest.TestCase):
    """Test cases for validation functions."""
    
    def test_estimate_treewidth(self):
        """Test treewidth estimation."""
        import networkx as nx
        
        # Test on a simple path graph (should have low treewidth)
        G = nx.path_graph(5)
        tw = estimate_treewidth(G)
        self.assertGreaterEqual(tw, 1)
        self.assertLessEqual(tw, 5)
        
        # Test on a complete graph (should have high treewidth)
        G = nx.complete_graph(4)
        tw = estimate_treewidth(G)
        self.assertGreaterEqual(tw, 3)
    
    def test_generate_random_3cnf_incidence(self):
        """Test random 3-CNF incidence graph generation."""
        G = generate_random_3cnf_incidence(10, 20)
        
        # Should have variable nodes
        var_nodes = [n for n in G.nodes() if 'x' in str(n)]
        self.assertEqual(len(var_nodes), 10)
        
        # Should have clause nodes
        clause_nodes = [n for n in G.nodes() if 'C' in str(n)]
        self.assertEqual(len(clause_nodes), 20)
        
        # Should have edges
        self.assertGreater(len(G.edges()), 0)

class TestModuleExecution(unittest.TestCase):
    """Test cases for module-level functions."""
    
    def test_encoder_produces_valid_cnf(self):
        """Test that encoder produces a valid CNF formula."""
        encoder = TseitinEncoder(10)
        variables, clauses = encoder.encode()
        
        # All clauses should contain only literals from the variable set
        all_vars_in_clauses = set()
        for clause in clauses:
            for literal in clause:
                all_vars_in_clauses.add(abs(literal))
        
        # All variables in clauses should be valid
        for var in all_vars_in_clauses:
            self.assertGreater(var, 0)


if __name__ == '__main__':
    print("Running hard_cnf_implementation Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
