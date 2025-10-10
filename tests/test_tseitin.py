"""
Unit tests for Tseitin formula generator

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import networkx as nx
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.gadgets.tseitin_generator import TseitinGenerator, generate_expander_tseitin, generate_ramanujan_expander, create_treewidth_hard_instance


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
    
    def test_generate_ramanujan_expander(self):
        """Test Ramanujan-like expander generation."""
        G = generate_ramanujan_expander(10, d=3)
        
        self.assertEqual(G.number_of_nodes(), 10)
        # Check it's 3-regular
        for node in G.nodes():
            self.assertEqual(G.degree(node), 3)
    
    def test_create_treewidth_hard_instance(self):
        """Test creation of treewidth-hard instance."""
        base_clauses = [[1, 2], [-1, 3]]
        combined, total_vars = create_treewidth_hard_instance(base_clauses, expander_size=10, d=3)
        
        self.assertGreater(len(combined), len(base_clauses))
        self.assertGreater(total_vars, 3)


if __name__ == '__main__':
    print("Running Tseitin Generator Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
