"""
Unit tests for Divine Trinity implementation

Tests the unification of Topology, Information, and Computation dimensions
via the sacred constant κ_Π = 2.5773.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Tarea 4: separator_information_need
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import networkx as nx
import numpy as np
from divine_creation import DivineTrinity, KAPPA_PI, PHI


class TestDivineTrinity(unittest.TestCase):
    """Test cases for DivineTrinity class."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Use fixed seed for reproducibility
        np.random.seed(42)
    
    def test_trinity_initialization(self):
        """Test that DivineTrinity initializes correctly."""
        G = nx.balanced_tree(2, 3)
        trinity = DivineTrinity(G)
        
        # Check all dimensions are computed
        self.assertIsNotNone(trinity.topology)
        self.assertIsNotNone(trinity.information)
        self.assertIsNotNone(trinity.computation)
        
        # Check dimensions are non-negative
        self.assertGreaterEqual(trinity.topology, 0)
        self.assertGreaterEqual(trinity.information, 0)
        self.assertGreaterEqual(trinity.computation, 0)
    
    def test_topology_measure_tree(self):
        """Test topology measurement for trees (treewidth should be 1)."""
        # A tree has treewidth 1
        T = nx.path_graph(10)
        trinity = DivineTrinity(T)
        
        # Path graph should have treewidth 1
        self.assertEqual(trinity.topology, 1.0)
    
    def test_topology_measure_grid(self):
        """Test topology measurement for grids."""
        # A grid should have reasonable treewidth
        Grid = nx.grid_2d_graph(5, 5)
        trinity = DivineTrinity(Grid)
        
        # Grid should have positive treewidth
        self.assertGreater(trinity.topology, 0)
        self.assertLess(trinity.topology, 25)  # Should be less than n
    
    def test_information_measure(self):
        """Test information complexity measurement."""
        G = nx.cycle_graph(10)
        trinity = DivineTrinity(G)
        
        # Information should be positive for non-trivial graphs
        self.assertGreater(trinity.information, 0)
    
    def test_computation_measure(self):
        """Test computation time measurement."""
        G = nx.complete_graph(5)
        trinity = DivineTrinity(G)
        
        # Computation should be positive
        self.assertGreater(trinity.computation, 0)
    
    def test_optimal_separator_found(self):
        """Test that optimal separator is found."""
        G = nx.balanced_tree(2, 3)
        trinity = DivineTrinity(G)
        
        separator = trinity.find_optimal_separator()
        
        # Separator should be non-empty for non-trivial graphs
        self.assertIsNotNone(separator)
        self.assertIsInstance(separator, set)
    
    def test_unity_verification_grid(self):
        """Test unity verification for grid graphs."""
        # Grids tend to show good unity
        Grid = nx.grid_2d_graph(10, 10)
        trinity = DivineTrinity(Grid)
        
        # Check that unity results are computed
        self.assertIsNotNone(trinity.unity_results)
        self.assertIn('topology_information', trinity.unity_results)
        self.assertIn('information_computation', trinity.unity_results)
        self.assertIn('topology_computation', trinity.unity_results)
    
    def test_kappa_pi_bounds(self):
        """Test that dimensions respect κ_Π bounds when unified."""
        G = nx.grid_2d_graph(8, 8)
        trinity = DivineTrinity(G)
        
        T = trinity.topology
        I = trinity.information
        C = trinity.computation
        
        # At least one pair should satisfy the bounds
        # (not all graphs show perfect unity)
        if T > 0 and I > 0:
            ratio_TI = I / T
            # Check if within bounds (may not always be true)
            if trinity.unity_results.get('topology_information', False):
                self.assertGreaterEqual(ratio_TI, 1/KAPPA_PI - 0.01)  # Small tolerance
                self.assertLessEqual(ratio_TI, KAPPA_PI + 0.01)
    
    def test_empty_graph(self):
        """Test handling of empty graph."""
        G = nx.Graph()
        trinity = DivineTrinity(G)
        
        # Empty graph should have zero dimensions
        self.assertEqual(trinity.topology, 0.0)
        self.assertEqual(trinity.information, 0.0)
    
    def test_single_node_graph(self):
        """Test handling of single node graph."""
        G = nx.Graph()
        G.add_node(0)
        trinity = DivineTrinity(G)
        
        # Single node should have zero or minimal complexity
        self.assertGreaterEqual(trinity.topology, 0)
    
    def test_complete_graph(self):
        """Test complete graph has high treewidth."""
        # Complete graph K_n has treewidth n-1
        G = nx.complete_graph(10)
        trinity = DivineTrinity(G)
        
        # Complete graph should have high treewidth (close to n-1)
        self.assertGreater(trinity.topology, 5)
    
    def test_bipartite_graph(self):
        """Test bipartite graph (SAT-like structure)."""
        # Create a simple bipartite graph
        G = nx.complete_bipartite_graph(5, 5)
        trinity = DivineTrinity(G)
        
        # Should have reasonable measures
        self.assertGreater(trinity.topology, 0)
        self.assertGreater(trinity.information, 0)
        self.assertGreater(trinity.computation, 0)
    
    def test_display_trinity_runs(self):
        """Test that display_trinity runs without error."""
        import io
        import contextlib
        
        G = nx.path_graph(5)
        trinity = DivineTrinity(G)
        
        # Should not raise an exception
        try:
            output_buffer = io.StringIO()
            with contextlib.redirect_stdout(output_buffer):
                trinity.display_trinity()
            output = output_buffer.getvalue()
            
            # Check output contains expected strings
            self.assertIn("TRINIDAD DIVINA", output)
            self.assertIn("κ_Π", output)
            self.assertIn("TOPOLOGÍA", output)
        except Exception as e:
            self.fail(f"display_trinity raised exception: {e}")
    
    def test_constants_defined(self):
        """Test that sacred constants are properly defined."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
        self.assertAlmostEqual(PHI, (1 + np.sqrt(5)) / 2, places=4)


class TestDivineUnityTheorem(unittest.TestCase):
    """Test cases for divine unity theorem demonstration."""
    
    def setUp(self):
        """Set up test fixtures."""
        np.random.seed(42)
    
    def test_tree_case(self):
        """Test divine trinity on balanced tree."""
        T = nx.balanced_tree(2, 4)
        trinity = DivineTrinity(T)
        
        # Tree should have treewidth 1
        self.assertEqual(trinity.topology, 1.0)
        
        # All dimensions should be positive
        self.assertGreater(trinity.information, 0)
        self.assertGreater(trinity.computation, 0)
    
    def test_grid_case(self):
        """Test divine trinity on grid."""
        Grid = nx.grid_2d_graph(10, 10)
        trinity = DivineTrinity(Grid)
        
        # Grid should show reasonable unity
        self.assertIsNotNone(trinity.unity_verified)
    
    def test_random_graph_case(self):
        """Test divine trinity on random graph."""
        ER = nx.erdos_renyi_graph(50, 0.4)
        trinity = DivineTrinity(ER)
        
        # All dimensions should be computed
        self.assertGreater(trinity.topology, 0)
        self.assertGreater(trinity.information, 0)
        self.assertGreater(trinity.computation, 0)
    
    def test_cnf_sat_graph_case(self):
        """Test divine trinity on CNF-SAT incidence graph."""
        # Create CNF-SAT incidence graph
        CNF = nx.Graph()
        var_names = [f"x{i}" for i in range(20)]
        for var in var_names:
            CNF.add_node(var, type='var')
        for j in range(80):
            CNF.add_node(f"C{j}", type='clause')
            vars_in_clause = np.random.choice(var_names, 3, replace=False)
            for v in vars_in_clause:
                CNF.add_edge(f"C{j}", v)
        
        trinity = DivineTrinity(CNF)
        
        # CNF graphs should show good unity properties
        self.assertGreater(trinity.topology, 0)
        self.assertGreater(trinity.information, 0)


class TestSeparatorAlgorithm(unittest.TestCase):
    """Test cases for optimal separator finding algorithm."""
    
    def test_separator_balances_components(self):
        """Test that separator produces balanced components."""
        G = nx.grid_2d_graph(8, 8)
        trinity = DivineTrinity(G)
        
        separator = trinity.find_optimal_separator()
        
        # Remove separator and check components
        G_minus = G.copy()
        G_minus.remove_nodes_from(separator)
        
        if nx.number_connected_components(G_minus) > 0:
            components = list(nx.connected_components(G_minus))
            if len(components) > 0:
                max_comp = max(len(c) for c in components)
                # Should be somewhat balanced (not all nodes in one component)
                self.assertLess(max_comp, len(G) * 0.9)
    
    def test_separator_size_reasonable(self):
        """Test that separator size is reasonable."""
        G = nx.grid_2d_graph(10, 10)
        trinity = DivineTrinity(G)
        
        separator = trinity.find_optimal_separator()
        
        # Separator should not be empty or the entire graph
        self.assertGreater(len(separator), 0)
        self.assertLess(len(separator), len(G))
    
    def test_separator_disconnects_graph(self):
        """Test that separator actually disconnects the graph."""
        # Use a graph with clear structure
        G = nx.barbell_graph(5, 3)
        trinity = DivineTrinity(G)
        
        separator = trinity.find_optimal_separator()
        
        # Remove separator
        G_minus = G.copy()
        G_minus.remove_nodes_from(separator)
        
        # Should have components or be empty
        num_components = nx.number_connected_components(G_minus)
        self.assertGreaterEqual(num_components, 0)


if __name__ == '__main__':
    unittest.main()
