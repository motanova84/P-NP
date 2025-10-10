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

from src.gadgets.tseitin_generator import TseitinGenerator, generate_expander_tseitin


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


if __name__ == '__main__':
    print("Running Tseitin Generator Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
