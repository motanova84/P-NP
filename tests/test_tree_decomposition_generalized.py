#!/usr/bin/env python3
"""
Tests for generalized tree decomposition across multiple graph families.

Extends tree decomposition to:
- Wheel graphs
- Ladder graphs
- Hypercube graphs
- Triangulated graphs
- Chordal graphs

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import unittest
import numpy as np
import networkx as nx
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import tree decomposition if available
try:
    from tree_decomposition_from_separator import TreeDecompositionBuilder
except ImportError:
    TreeDecompositionBuilder = None


class TestTreeDecompositionWheelGraphs(unittest.TestCase):
    """Test tree decomposition on wheel graphs."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_wheel_graph_small(self):
        """Test tree decomposition on small wheel graph."""
        # Wheel graph: cycle + center vertex connected to all
        G = nx.wheel_graph(6)  # 5-cycle + center (6 vertices total)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        # Verify tree decomposition properties
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Wheel graph W_n has treewidth 3 for n >= 4
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 4)  # Greedy might not be optimal
    
    def test_wheel_graph_medium(self):
        """Test tree decomposition on medium wheel graph."""
        G = nx.wheel_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        width = builder.compute_width(decomposition)
        # Wheel graphs have treewidth 3
        self.assertLessEqual(width, 5)
    
    def test_wheel_graph_treewidth_bound(self):
        """Test that wheel graphs have bounded treewidth."""
        # Test multiple wheel graphs
        for n in [5, 7, 9, 12]:
            G = nx.wheel_graph(n)
            builder = TreeDecompositionBuilder(G)
            decomposition = builder.build_tree_decomposition()
            
            self.assertTrue(builder.verify_tree_decomposition(decomposition))
            width = builder.compute_width(decomposition)
            
            # Wheel graphs should have treewidth 3
            # Our greedy algorithm might give slightly higher
            self.assertLessEqual(width, 5,
                msg=f"Wheel graph W_{n} has unexpectedly high treewidth")


class TestTreeDecompositionLadderGraphs(unittest.TestCase):
    """Test tree decomposition on ladder graphs."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_ladder_graph_small(self):
        """Test tree decomposition on small ladder graph."""
        G = nx.ladder_graph(5)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Ladder graph has treewidth 2
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 3)
    
    def test_ladder_graph_medium(self):
        """Test tree decomposition on medium ladder graph."""
        G = nx.ladder_graph(12)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 3)
    
    def test_ladder_graph_treewidth_constant(self):
        """Test that ladder graphs have constant treewidth."""
        # Test multiple sizes
        for n in [4, 8, 16, 20]:
            G = nx.ladder_graph(n)
            builder = TreeDecompositionBuilder(G)
            decomposition = builder.build_tree_decomposition()
            
            width = builder.compute_width(decomposition)
            
            # Ladder graphs have treewidth 2 regardless of size
            self.assertLessEqual(width, 3,
                msg=f"Ladder graph of length {n} has treewidth > 3")


class TestTreeDecompositionHypercubes(unittest.TestCase):
    """Test tree decomposition on hypercube graphs."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_hypercube_2d(self):
        """Test tree decomposition on 2D hypercube (square)."""
        G = nx.hypercube_graph(2)  # 4 vertices, square
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # 2D hypercube (cycle) has treewidth 2
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 2)
    
    def test_hypercube_3d(self):
        """Test tree decomposition on 3D hypercube (cube)."""
        G = nx.hypercube_graph(3)  # 8 vertices, cube
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # 3D hypercube has treewidth 3
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 4)
    
    def test_hypercube_4d(self):
        """Test tree decomposition on 4D hypercube."""
        G = nx.hypercube_graph(4)  # 16 vertices
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # 4D hypercube has treewidth 4
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 6)
    
    def test_hypercube_treewidth_growth(self):
        """Test that hypercube treewidth grows with dimension."""
        widths = []
        for d in [2, 3, 4]:
            G = nx.hypercube_graph(d)
            builder = TreeDecompositionBuilder(G)
            decomposition = builder.build_tree_decomposition()
            
            width = builder.compute_width(decomposition)
            widths.append(width)
        
        # Treewidth should generally increase with dimension
        # (though greedy algorithm might not always be monotonic)
        self.assertGreater(widths[-1], widths[0],
            "Higher dimensional hypercubes should have higher treewidth")


class TestTreeDecompositionChordalGraphs(unittest.TestCase):
    """Test tree decomposition on chordal graphs."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_tree_is_chordal(self):
        """Test that trees are chordal (treewidth 1)."""
        G = nx.balanced_tree(2, 3)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Trees have treewidth 1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 1)
    
    def test_complete_graph_is_chordal(self):
        """Test tree decomposition on complete graph (chordal)."""
        # Complete graphs are chordal
        G = nx.complete_graph(7)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # K_n has treewidth n-1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 6)
    
    def test_interval_graph_is_chordal(self):
        """Test tree decomposition on interval graph (chordal)."""
        # Create an interval graph (path graph is interval graph)
        G = nx.path_graph(10)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Path graph has treewidth 1
        width = builder.compute_width(decomposition)
        self.assertEqual(width, 1)


class TestTreeDecompositionPlanarGraphs(unittest.TestCase):
    """Test tree decomposition on planar graphs."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_outerplanar_graph(self):
        """Test tree decomposition on outerplanar graph."""
        # Cycle graphs are outerplanar
        G = nx.cycle_graph(8)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Outerplanar graphs have treewidth ≤ 2
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 2)
    
    def test_grid_graph_planar(self):
        """Test tree decomposition on grid graph (planar)."""
        G = nx.grid_2d_graph(4, 4)
        G = nx.convert_node_labels_to_integers(G)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Grid graphs have treewidth min(width, height)
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 6)


class TestTreeDecompositionGeneralizedFamilies(unittest.TestCase):
    """Test tree decomposition on various graph families."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_barbell_graph(self):
        """Test tree decomposition on barbell graph."""
        # Two complete graphs connected by a path
        G = nx.barbell_graph(5, 2)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
        
        # Treewidth should be close to that of K5 (which is 4)
        width = builder.compute_width(decomposition)
        self.assertLessEqual(width, 6)
    
    def test_lollipop_graph(self):
        """Test tree decomposition on lollipop graph."""
        # Complete graph connected to a path
        G = nx.lollipop_graph(4, 5)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_circular_ladder_graph(self):
        """Test tree decomposition on circular ladder graph."""
        G = nx.circular_ladder_graph(6)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))
    
    def test_dorogovtsev_goltsev_mendes_graph(self):
        """Test tree decomposition on fractal graph."""
        G = nx.dorogovtsev_goltsev_mendes_graph(3)
        builder = TreeDecompositionBuilder(G)
        decomposition = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomposition))


class TestTreeDecompositionParameterizedFamilies(unittest.TestCase):
    """Test tree decomposition behavior across parameterized families."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_treewidth_bounded_for_bounded_degree(self):
        """Test that bounded-degree graphs can have various treewidths."""
        # 3-regular graphs: cycle (tw=2), Petersen (tw=4)
        G_cycle = nx.cycle_graph(10)
        G_petersen = nx.petersen_graph()
        
        builder_cycle = TreeDecompositionBuilder(G_cycle)
        builder_petersen = TreeDecompositionBuilder(G_petersen)
        
        decomp_cycle = builder_cycle.build_tree_decomposition()
        decomp_petersen = builder_petersen.build_tree_decomposition()
        
        width_cycle = builder_cycle.compute_width(decomp_cycle)
        width_petersen = builder_petersen.compute_width(decomp_petersen)
        
        # Petersen should have higher treewidth than cycle
        # (both are 3-regular)
        self.assertGreater(width_petersen, width_cycle)
    
    def test_treewidth_for_different_densities(self):
        """Test tree decomposition on graphs with different edge densities."""
        n = 12
        
        # Sparse: path
        G_sparse = nx.path_graph(n)
        # Medium: cycle
        G_medium = nx.cycle_graph(n)
        # Dense: complete
        G_dense = nx.complete_graph(n)
        
        builders = [
            TreeDecompositionBuilder(G_sparse),
            TreeDecompositionBuilder(G_medium),
            TreeDecompositionBuilder(G_dense)
        ]
        
        widths = []
        for builder in builders:
            decomp = builder.build_tree_decomposition()
            self.assertTrue(builder.verify_tree_decomposition(decomp))
            widths.append(builder.compute_width(decomp))
        
        # Treewidth should increase with density
        self.assertLess(widths[0], widths[2])


class TestTreeDecompositionSpecialStructures(unittest.TestCase):
    """Test tree decomposition on graphs with special structures."""
    
    def setUp(self):
        """Check if tree decomposition module is available."""
        if TreeDecompositionBuilder is None:
            self.skipTest("TreeDecompositionBuilder not available")
    
    def test_k_tree(self):
        """Test tree decomposition on k-trees."""
        # A k-tree has treewidth exactly k
        # Complete graph K_{k+1} is a k-tree
        for k in [2, 3, 4]:
            G = nx.complete_graph(k + 1)
            builder = TreeDecompositionBuilder(G)
            decomp = builder.build_tree_decomposition()
            
            width = builder.compute_width(decomp)
            self.assertEqual(width, k,
                msg=f"K_{k+1} should have treewidth {k}")
    
    def test_series_parallel_graph(self):
        """Test tree decomposition on series-parallel graph."""
        # Ladder graphs are series-parallel
        G = nx.ladder_graph(8)
        builder = TreeDecompositionBuilder(G)
        decomp = builder.build_tree_decomposition()
        
        # Series-parallel graphs have treewidth ≤ 2
        width = builder.compute_width(decomp)
        self.assertLessEqual(width, 2)
    
    def test_cactus_graph(self):
        """Test tree decomposition on cactus graph."""
        # Cactus: each edge is in at most one cycle
        # Simple cactus: cycle with a path attached
        G = nx.cycle_graph(6)
        # Add a path
        G.add_edges_from([(0, 6), (6, 7), (7, 8)])
        
        builder = TreeDecompositionBuilder(G)
        decomp = builder.build_tree_decomposition()
        
        self.assertTrue(builder.verify_tree_decomposition(decomp))
        
        # Cactus graphs have treewidth ≤ 2
        width = builder.compute_width(decomp)
        self.assertLessEqual(width, 2)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == '__main__':
    run_tests()
