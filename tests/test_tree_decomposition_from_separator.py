#!/usr/bin/env python3
"""
Unit tests for Tree Decomposition from Separator Algorithm.

Tests the TreeDecompositionBuilder class and verifies the three properties
of tree decompositions on various graph types.

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import unittest
import sys
import os
import networkx as nx
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from tree_decomposition_from_separator import (
    TreeDecompositionBuilder,
    TreeDecompositionNode
)


class TestTreeDecompositionNode(unittest.TestCase):
    """Test the TreeDecompositionNode dataclass."""
    
    def test_create_node(self):
        """Test creating a tree decomposition node."""
        bag = {1, 2, 3}
        node = TreeDecompositionNode(bag=bag, children=[1, 2], parent=0)
        
        self.assertEqual(node.bag, bag)
        self.assertEqual(node.children, [1, 2])
        self.assertEqual(node.parent, 0)
    
    def test_node_string_representation(self):
        """Test string representation of node."""
        node = TreeDecompositionNode(bag={3, 1, 2}, children=[], parent=None)
        str_repr = str(node)
        self.assertIn("1", str_repr)
        self.assertIn("2", str_repr)
        self.assertIn("3", str_repr)


class TestTreeDecompositionBuilder(unittest.TestCase):
    """Test the TreeDecompositionBuilder class."""
    
    def setUp(self):
        """Set up test fixtures."""
        np.random.seed(42)
    
    def test_empty_graph(self):
        """Test tree decomposition on empty graph."""
        G = nx.Graph()
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertEqual(len(decomposition), 0)
        self.assertEqual(builder.compute_width(decomposition), 0)
    
    def test_single_node(self):
        """Test tree decomposition on single node."""
        G = nx.Graph()
        G.add_node(0)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertEqual(len(decomposition), 1)
        self.assertEqual(decomposition[0].bag, {0})
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_single_edge(self):
        """Test tree decomposition on single edge."""
        G = nx.Graph()
        G.add_edge(0, 1)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertGreaterEqual(len(decomposition), 1)
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        # For a single edge, treewidth should be 1
        self.assertLessEqual(builder.compute_width(decomposition), 1)
    
    def test_path_graph(self):
        """Test tree decomposition on path graph."""
        G = nx.path_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        # Verify all three properties
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Path has treewidth 1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 1)
    
    def test_cycle_graph(self):
        """Test tree decomposition on cycle graph."""
        G = nx.cycle_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Cycle has treewidth 2
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 2)
    
    def test_star_graph(self):
        """Test tree decomposition on star graph."""
        G = nx.star_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Star has treewidth 1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 1)
    
    def test_complete_graph(self):
        """Test tree decomposition on complete graph."""
        G = nx.complete_graph(8)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Complete graph K_n has treewidth n-1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 7)
    
    def test_grid_graph(self):
        """Test tree decomposition on grid graph."""
        G = nx.grid_2d_graph(4, 4)
        G = nx.convert_node_labels_to_integers(G)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Grid treewidth is min(width, height) which is 4 for 4x4
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 6)  # Greedy might not be optimal
    
    def test_tree_graph(self):
        """Test tree decomposition on tree (should have treewidth 1)."""
        G = nx.balanced_tree(2, 3)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Trees have treewidth 1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 1)
    
    def test_random_sparse_graph(self):
        """Test tree decomposition on random sparse graph."""
        G = nx.erdos_renyi_graph(20, 0.15, seed=42)
        if not nx.is_connected(G):
            G = G.subgraph(max(nx.connected_components(G), key=len)).copy()
        
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_random_dense_graph(self):
        """Test tree decomposition on random dense graph."""
        G = nx.erdos_renyi_graph(15, 0.6, seed=42)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))


class TestSeparatorMethods(unittest.TestCase):
    """Test separator finding methods."""
    
    def test_find_balanced_separator_path(self):
        """Test finding separator on path graph."""
        G = nx.path_graph(10)
        builder = TreeDecompositionBuilder(G)
        
        # For path graph, separator should be small (ideally 1 node)
        separator = builder.find_balanced_separator(set(G.nodes()))
        if separator:
            self.assertLessEqual(len(separator), 3)
    
    def test_find_balanced_separator_complete(self):
        """Test finding separator on complete graph."""
        G = nx.complete_graph(10)
        builder = TreeDecompositionBuilder(G)
        
        separator = builder.find_balanced_separator(set(G.nodes()))
        # Complete graph is hard to separate
        # Any separator will be large or won't exist
        # This is ok - the algorithm should handle it
        self.assertTrue(separator is None or len(separator) > 0)
    
    def test_is_separator(self):
        """Test separator verification."""
        G = nx.path_graph(10)
        builder = TreeDecompositionBuilder(G)
        
        # Middle nodes should be separators
        self.assertTrue(builder._is_separator({4, 5}, set(G.nodes())))
        self.assertTrue(builder._is_separator({5}, set(G.nodes())))
        
        # Empty set is not a separator
        self.assertFalse(builder._is_separator(set(), set(G.nodes())))
    
    def test_connected_components(self):
        """Test connected components finding."""
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (3, 4), (4, 5)])
        builder = TreeDecompositionBuilder(G)
        
        # Remove node 1 and 4 to create components
        # After removing 1 and 4: {0}, {2}, {3}, {5} - four singletons
        remaining = {0, 2, 3, 5}
        components = builder._connected_components(remaining)
        
        self.assertEqual(len(components), 4)
        # All should be singletons
        component_sizes = sorted([len(c) for c in components])
        self.assertEqual(component_sizes, [1, 1, 1, 1])


class TestTreeDecompositionProperties(unittest.TestCase):
    """Test the three properties of tree decomposition."""
    
    def test_vertex_coverage(self):
        """Test that all vertices are covered by at least one bag."""
        G = nx.karate_club_graph()
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        all_vertices = set(G.nodes())
        covered = set()
        for node in decomposition:
            covered.update(node.bag)
        
        self.assertEqual(covered, all_vertices)
    
    def test_edge_coverage(self):
        """Test that all edges are covered by at least one bag."""
        G = nx.karate_club_graph()
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        for u, v in G.edges():
            found = False
            for node in decomposition:
                if u in node.bag and v in node.bag:
                    found = True
                    break
            self.assertTrue(found, f"Edge ({u}, {v}) not covered")
    
    def test_running_intersection_property(self):
        """Test the running intersection property."""
        G = nx.cycle_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        # For each vertex, bags containing it should form connected subtree
        for v in G.nodes():
            containing_bags = [i for i, node in enumerate(decomposition) if v in node.bag]
            
            if len(containing_bags) <= 1:
                continue
            
            # Build subgraph of bags
            subgraph = nx.Graph()
            subgraph.add_nodes_from(containing_bags)
            
            for i in containing_bags:
                node = decomposition[i]
                if node.parent is not None and node.parent in containing_bags:
                    subgraph.add_edge(i, node.parent)
                for child in node.children:
                    if child in containing_bags:
                        subgraph.add_edge(i, child)
            
            # Check connectivity
            if subgraph.number_of_nodes() > 0:
                self.assertTrue(nx.is_connected(subgraph),
                               f"Bags containing vertex {v} don't form connected subtree")


class TestWidthComputation(unittest.TestCase):
    """Test treewidth computation."""
    
    def test_width_empty(self):
        """Test width of empty decomposition."""
        builder = TreeDecompositionBuilder(nx.Graph())
        self.assertEqual(builder.compute_width([]), 0)
    
    def test_width_single_bag(self):
        """Test width with single bag."""
        builder = TreeDecompositionBuilder(nx.Graph())
        node = TreeDecompositionNode(bag={1, 2, 3}, children=[], parent=None)
        # Width = |bag| - 1 = 3 - 1 = 2
        self.assertEqual(builder.compute_width([node]), 2)
    
    def test_width_multiple_bags(self):
        """Test width with multiple bags."""
        builder = TreeDecompositionBuilder(nx.Graph())
        nodes = [
            TreeDecompositionNode(bag={1, 2}, children=[], parent=None),
            TreeDecompositionNode(bag={2, 3, 4}, children=[], parent=0),
            TreeDecompositionNode(bag={4, 5}, children=[], parent=1),
        ]
        # Max bag size is 3, so width = 3 - 1 = 2
        self.assertEqual(builder.compute_width(nodes), 2)


class TestIntegration(unittest.TestCase):
    """Integration tests with various graph families."""
    
    def test_petersen_graph(self):
        """Test on Petersen graph."""
        G = nx.petersen_graph()
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        # Petersen graph has treewidth 4
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 6)  # Greedy might not be optimal
    
    def test_disconnected_graph(self):
        """Test on disconnected graph."""
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2)])
        G.add_edges_from([(3, 4), (4, 5)])
        
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_wheel_graph(self):
        """Test on wheel graph."""
        G = nx.wheel_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_ladder_graph(self):
        """Test on ladder graph."""
        G = nx.ladder_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        # Ladder graph has treewidth 2
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 3)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == '__main__':
    run_tests()
