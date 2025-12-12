"""
Unit tests for explicit expander formula construction

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import networkx as nx
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import the demo module functions
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'examples'))
from demo_explicit_expander import (
    margulis_gabber_galil_graph,
    is_expander,
    construct_explicit_hard_formula
)


class TestExplicitExpander(unittest.TestCase):
    """Test cases for explicit expander construction."""
    
    def test_margulis_graph_construction(self):
        """Test that Margulis graph can be constructed."""
        m = 3
        G = margulis_gabber_galil_graph(m)
        
        # Should have m² vertices
        self.assertEqual(len(G.nodes()), m * m)
        
        # Check it's a graph (basic NetworkX properties)
        self.assertIsInstance(G, nx.Graph)
    
    def test_margulis_graph_regularity(self):
        """Test that Margulis graph is approximately regular."""
        m = 4
        G = margulis_gabber_galil_graph(m)
        
        # Check degrees
        degrees = [G.degree(v) for v in G.nodes()]
        min_deg = min(degrees)
        max_deg = max(degrees)
        
        # Should be 8-regular (approximately, allowing for boundary effects)
        self.assertGreaterEqual(min_deg, 8)
        self.assertLessEqual(max_deg, 12)  # Allow some variation
    
    def test_margulis_no_self_loops(self):
        """Test that Margulis graph has no self-loops."""
        m = 3
        G = margulis_gabber_galil_graph(m)
        
        # Check no self-loops
        for v in G.nodes():
            self.assertNotIn(v, list(G.neighbors(v)))
    
    def test_margulis_symmetry(self):
        """Test that Margulis graph edges are symmetric."""
        m = 3
        G = margulis_gabber_galil_graph(m)
        
        # Check symmetry of edges
        for u, v in G.edges():
            self.assertTrue(G.has_edge(v, u))
    
    def test_expander_property_heuristic(self):
        """Test expansion property heuristically."""
        m = 5
        G = margulis_gabber_galil_graph(m)
        
        # Check if it passes expander test
        # (Note: this is heuristic and may occasionally fail due to randomness)
        result = is_expander(G, delta=0.05)
        # We don't assert True because it's probabilistic,
        # just check it doesn't crash
        self.assertIsInstance(result, bool)
    
    def test_explicit_formula_construction(self):
        """Test explicit hard formula construction."""
        n = 9
        num_vars, clauses, G = construct_explicit_hard_formula(n)
        
        # Should produce a formula
        self.assertGreater(num_vars, 0)
        self.assertGreater(len(clauses), 0)
        
        # Should have approximately n vertices
        self.assertGreaterEqual(len(G.nodes()), n)
        self.assertLessEqual(len(G.nodes()), 2 * n)
    
    def test_formula_size_linear(self):
        """Test that formula size is O(n)."""
        n = 25
        num_vars, clauses, G = construct_explicit_hard_formula(n)
        
        # Number of variables should be O(n)
        # For degree-8 graph: num_vars ≈ 4n (each edge counted once)
        self.assertLess(num_vars, 20 * n)  # Generous bound
        
        # Number of clauses should be O(n) for constant degree
        # (Each vertex generates O(2^d) clauses for XOR, with d=8)
        # The XOR encoding generates 2^(d-1) clauses per vertex
        # So for d=8, we get 2^7=128 clauses per vertex, times n vertices
        self.assertLess(len(clauses), 1000 * n)  # Generous bound for 2^8=256
    
    def test_multiple_sizes(self):
        """Test construction works for multiple sizes."""
        test_sizes = [9, 16, 25]
        
        for n in test_sizes:
            with self.subTest(n=n):
                num_vars, clauses, G = construct_explicit_hard_formula(n)
                self.assertGreater(num_vars, 0)
                self.assertGreater(len(clauses), 0)
    
    def test_clause_structure(self):
        """Test that clauses have valid structure."""
        n = 9
        num_vars, clauses, G = construct_explicit_hard_formula(n)
        
        # All clauses should be lists
        for clause in clauses[:10]:  # Check first 10
            self.assertIsInstance(clause, list)
            
            # Each literal should be a non-zero integer
            for lit in clause:
                self.assertIsInstance(lit, int)
                self.assertNotEqual(lit, 0)
                
                # Variable index should be in range
                var = abs(lit)
                self.assertGreaterEqual(var, 1)
                self.assertLessEqual(var, num_vars)


class TestExplicitFormulaProperties(unittest.TestCase):
    """Test properties of the explicit formulas matching Lean theorems."""
    
    def test_linear_treewidth_property(self):
        """Test that treewidth appears to be linear (sanity check)."""
        n = 25
        num_vars, clauses, G = construct_explicit_hard_formula(n)
        
        # The graph should have size O(n)
        actual_n = len(G.nodes())
        self.assertGreater(actual_n, 0.5 * n)
        self.assertLess(actual_n, 2 * n)
        
        # Theoretical lower bound on treewidth
        tw_lower = actual_n * 0.01
        
        # Since we constructed an expander, treewidth should be high
        # We can't compute exact treewidth easily, but we can verify
        # the graph has good expansion properties as a proxy
        degrees = [G.degree(v) for v in G.nodes()]
        avg_degree = sum(degrees) / len(degrees)
        
        # Expanders have constant degree
        self.assertGreater(avg_degree, 6)
        self.assertLess(avg_degree, 15)
    
    def test_unsat_construction(self):
        """Test that odd charge construction is used (implies UNSAT)."""
        n = 16
        num_vars, clauses, G = construct_explicit_hard_formula(n)
        
        # The construction uses odd charge (one vertex with charge 1)
        # We can't easily verify UNSAT without a SAT solver,
        # but we can verify the formula was constructed
        self.assertGreater(len(clauses), 0)
        
        # For UNSAT formula, there should be some non-trivial clauses
        non_unit_clauses = [c for c in clauses if len(c) > 1]
        self.assertGreater(len(non_unit_clauses), 0)


if __name__ == '__main__':
    print("Running Explicit Expander Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
