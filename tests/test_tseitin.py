"""
Unit tests for Tseitin formula generator and IC-SAT

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import networkx as nx
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.gadgets.tseitin_generator import TseitinGenerator, generate_expander_tseitin
from src.computational_dichotomy import LargeScaleValidation, incidence_graph, primal_graph, estimate_treewidth


class TestTseitinGenerator(unittest.TestCase):
    """Test cases for Tseitin formula generation."""
    
    def test_basic_triangle(self):
        """Test Tseitin formula on a simple triangle graph."""
        # Create a triangle graph
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (2, 0)])
        
        generator = TseitinGenerator(G)
        
        # All even charges (satisfiable)
        num_vars, clauses = generator.generate_formula([0, 0, 0])
        self.assertEqual(num_vars, 3)  # 3 edges
        self.assertGreater(len(clauses), 0)
    
    def test_path_graph(self):
        """Test Tseitin formula on a path graph."""
        # Create a path: 0-1-2
        G = nx.path_graph(3)
        
        generator = TseitinGenerator(G)
        
        # Odd charges at endpoints (satisfiable)
        num_vars, clauses = generator.generate_formula([1, 0, 1])
        self.assertEqual(num_vars, 2)  # 2 edges in path
        self.assertGreater(len(clauses), 0)
    
    def test_expander_generation(self):
        """Test generation of Tseitin formula over expander."""
        num_vars, clauses = generate_expander_tseitin(6, 3)
        
        # Should have variables for each edge
        self.assertGreater(num_vars, 0)
        self.assertGreater(len(clauses), 0)
    
    def test_charge_assignment_length(self):
        """Test that charge assignment must match number of nodes."""
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2)])
        
        generator = TseitinGenerator(G)
        
        # Wrong length should raise error
        with self.assertRaises(ValueError):
            generator.generate_formula([0, 0])  # Should be 3 nodes


class TestICLargeScaleValidation(unittest.TestCase):
    """Test cases for IC-SAT and Large Scale Validation."""
    
    def test_small_ic_sat(self):
        """Test IC-SAT on a small instance."""
        lsv = LargeScaleValidation()
        # Should run without errors
        lsv.run_ic_sat(10)
        # No assertion needed, just checking it doesn't crash
    
    def test_generate_3sat_critical(self):
        """Test generation of 3-SAT critical formulas."""
        lsv = LargeScaleValidation()
        clauses = lsv.generate_3sat_critical(10, ratio=4.2)
        
        # Should have approximately 4.2 * n clauses
        self.assertGreater(len(clauses), 30)
        self.assertLess(len(clauses), 50)
        
        # Each clause should have 3 literals
        for clause in clauses:
            self.assertEqual(len(clause), 3)
    
    def test_estimate_treewidth_practical(self):
        """Test practical treewidth estimation."""
        lsv = LargeScaleValidation()
        tw = lsv.estimate_treewidth_practical(n=20)
        
        # Treewidth should be a positive integer
        self.assertGreater(tw, 0)
    
    def test_incidence_graph(self):
        """Test incidence graph construction."""
        clauses = [[1, 2, 3], [-1, 2], [3, -4]]
        G = incidence_graph(4, clauses)
        
        # Should have 4 variable nodes + 3 clause nodes
        self.assertEqual(len(G.nodes()), 7)
        
        # Check bipartite structure
        var_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 0]
        clause_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
        self.assertEqual(len(var_nodes), 4)
        self.assertEqual(len(clause_nodes), 3)
    
    def test_primal_graph(self):
        """Test primal graph construction."""
        clauses = [[1, 2, 3], [-1, 2], [3, -4]]
        G = primal_graph(4, clauses)
        
        # Should have 4 variable nodes
        self.assertEqual(len(G.nodes()), 4)
        
        # Should have edges between variables in the same clause
        self.assertTrue(G.has_edge('v1', 'v2'))
        self.assertTrue(G.has_edge('v2', 'v3'))


if __name__ == '__main__':
    print("Running Tseitin Generator and IC-SAT Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
