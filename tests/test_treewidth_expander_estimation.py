#!/usr/bin/env python3
"""
Unit tests for treewidth_expander_estimation.py

Tests the functions that generate expander graphs and estimate their treewidth
to validate the theoretical prediction that treewidth(G) ∈ Ω(n).

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
import unittest
import networkx as nx

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from experiments.treewidth_expander_estimation import (
    generate_expander,
    estimate_treewidth_greedy_fillin,
    run_experiment,
    display_results,
    plot_results
)


class TestExpanderGeneration(unittest.TestCase):
    """Test expander graph generation."""
    
    def test_generate_expander_basic(self):
        """Test basic expander generation."""
        G = generate_expander(n=20, d=3)
        
        # Check properties
        self.assertEqual(len(G.nodes()), 20, "Graph should have correct number of nodes")
        self.assertTrue(nx.is_connected(G), "Graph should be connected")
        
        # Check regularity
        degrees = [G.degree(node) for node in G.nodes()]
        self.assertTrue(all(d == 3 for d in degrees), "All nodes should have degree 3")
    
    def test_generate_expander_different_sizes(self):
        """Test expander generation for different sizes."""
        for n in [10, 30, 50]:
            G = generate_expander(n=n, d=3)
            self.assertEqual(len(G.nodes()), n)
            self.assertTrue(nx.is_connected(G))
    
    def test_generate_expander_different_degrees(self):
        """Test expander generation with different degrees."""
        for d in [3, 4, 5]:
            G = generate_expander(n=20, d=d)
            degrees = [G.degree(node) for node in G.nodes()]
            self.assertTrue(all(deg == d for deg in degrees))


class TestTreewidthEstimation(unittest.TestCase):
    """Test treewidth estimation."""
    
    def test_estimate_treewidth_path(self):
        """Test treewidth estimation on a path graph (known tw=1)."""
        G = nx.path_graph(10)
        tw = estimate_treewidth_greedy_fillin(G)
        
        # Path graphs have treewidth 1
        self.assertEqual(tw, 1, "Path graph should have treewidth 1")
    
    def test_estimate_treewidth_complete(self):
        """Test treewidth estimation on a complete graph (known tw=n-1)."""
        n = 5
        G = nx.complete_graph(n)
        tw = estimate_treewidth_greedy_fillin(G)
        
        # Complete graph K_n has treewidth n-1
        self.assertEqual(tw, n - 1, f"Complete graph K_{n} should have treewidth {n-1}")
    
    def test_estimate_treewidth_cycle(self):
        """Test treewidth estimation on a cycle graph (known tw=2)."""
        G = nx.cycle_graph(10)
        tw = estimate_treewidth_greedy_fillin(G)
        
        # Cycle graphs have treewidth 2
        self.assertEqual(tw, 2, "Cycle graph should have treewidth 2")
    
    def test_estimate_treewidth_grid(self):
        """Test treewidth estimation on a grid graph."""
        G = nx.grid_2d_graph(3, 3)
        tw = estimate_treewidth_greedy_fillin(G)
        
        # Grid graph 3x3 should have treewidth 3
        self.assertEqual(tw, 3, "3x3 grid should have treewidth 3")
    
    def test_estimate_treewidth_positive(self):
        """Test that treewidth is always positive for non-trivial graphs."""
        G = generate_expander(n=20, d=3)
        tw = estimate_treewidth_greedy_fillin(G)
        
        self.assertGreater(tw, 0, "Treewidth should be positive")
        self.assertIsInstance(tw, int, "Treewidth should be an integer")


class TestExpanderTreewidthProperties(unittest.TestCase):
    """Test that expander graphs have the expected treewidth properties."""
    
    def test_expander_treewidth_linear_growth(self):
        """Test that treewidth grows approximately linearly with n."""
        sizes = [20, 40, 60]
        ratios = []
        
        for n in sizes:
            G = generate_expander(n=n, d=3)
            tw = estimate_treewidth_greedy_fillin(G)
            ratio = tw / n
            ratios.append(ratio)
        
        # Check that ratios are in a reasonable range (0.1 to 0.3)
        for ratio in ratios:
            self.assertGreater(ratio, 0.1, f"Ratio {ratio} should be > 0.1")
            self.assertLess(ratio, 0.3, f"Ratio {ratio} should be < 0.3")
        
        # Check that ratios don't vary too much (standard deviation check)
        avg_ratio = sum(ratios) / len(ratios)
        max_deviation = max(abs(r - avg_ratio) for r in ratios)
        self.assertLess(max_deviation, 0.15, "Ratios should be relatively consistent")


class TestExperimentExecution(unittest.TestCase):
    """Test the complete experiment execution."""
    
    def test_run_experiment_basic(self):
        """Test running the experiment with small sizes."""
        results = run_experiment(sizes=[20, 40], d=3)
        
        self.assertEqual(len(results), 2, "Should return results for 2 sizes")
        
        for n, tw, ratio in results:
            self.assertIsInstance(n, int, "n should be an integer")
            self.assertIsInstance(tw, int, "tw should be an integer")
            self.assertIsInstance(ratio, float, "ratio should be a float")
            self.assertGreater(tw, 0, "Treewidth should be positive")
            self.assertGreater(ratio, 0, "Ratio should be positive")
    
    def test_run_experiment_results_structure(self):
        """Test that experiment results have correct structure."""
        results = run_experiment(sizes=[30], d=3)
        
        self.assertEqual(len(results), 1)
        n, tw, ratio = results[0]
        
        # Verify the ratio calculation
        self.assertAlmostEqual(ratio, tw / n, places=6)
    
    def test_display_results_no_error(self):
        """Test that display_results doesn't raise errors."""
        results = [(50, 9, 0.18), (100, 18, 0.18)]
        
        # Should not raise any exceptions
        try:
            display_results(results)
        except Exception as e:
            self.fail(f"display_results raised an exception: {e}")
    
    def test_plot_results_no_error(self):
        """Test that plot_results doesn't raise errors."""
        results = [(50, 9, 0.18), (100, 18, 0.18)]
        
        # Should not raise any exceptions
        try:
            plot_results(results, output_file='/tmp/test_plot.png')
        except Exception as e:
            self.fail(f"plot_results raised an exception: {e}")


class TestExpanderGraphProperties(unittest.TestCase):
    """Test specific properties of the generated expander graphs."""
    
    def test_expander_connectivity(self):
        """Test that generated graphs are always connected."""
        for _ in range(5):  # Test multiple random instances
            G = generate_expander(n=30, d=3)
            self.assertTrue(nx.is_connected(G), "Expander should be connected")
    
    def test_expander_regularity(self):
        """Test that generated graphs are d-regular."""
        G = generate_expander(n=40, d=4)
        degrees = [G.degree(node) for node in G.nodes()]
        
        self.assertTrue(all(d == 4 for d in degrees), "Graph should be 4-regular")
    
    def test_expander_edge_count(self):
        """Test that expander has correct number of edges."""
        n = 50
        d = 3
        G = generate_expander(n=n, d=d)
        
        # For a d-regular graph on n nodes, number of edges = (n*d)/2
        expected_edges = (n * d) // 2
        actual_edges = len(G.edges())
        
        self.assertEqual(actual_edges, expected_edges, 
                        f"Graph should have {expected_edges} edges")


if __name__ == '__main__':
    unittest.main()
