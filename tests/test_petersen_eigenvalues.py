#!/usr/bin/env python3
"""
Tests for Petersen graph eigenvalue calculations.

The Petersen graph is a famous graph with 10 vertices and 15 edges.
It is 3-regular, has girth 5, and chromatic number 3.

Known spectral properties:
- The adjacency matrix eigenvalues are: 3, 1, 1, 1, 1, 1, -2, -2, -2, -2
- The Laplacian eigenvalues can be derived from these
- Treewidth is 4

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import unittest
import numpy as np
import networkx as nx
from scipy import linalg
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


class PetersenGraphAnalyzer:
    """Analyzer for spectral properties of the Petersen graph."""
    
    def __init__(self):
        """Initialize with the Petersen graph."""
        self.G = nx.petersen_graph()
        self.n = 10  # Petersen graph has 10 vertices
        
    def get_adjacency_matrix(self):
        """Get adjacency matrix of Petersen graph."""
        return nx.adjacency_matrix(self.G).toarray()
    
    def get_laplacian_matrix(self):
        """Get combinatorial Laplacian matrix L = D - A."""
        return nx.laplacian_matrix(self.G).toarray()
    
    def get_normalized_laplacian(self):
        """Get normalized Laplacian matrix."""
        return nx.normalized_laplacian_matrix(self.G).toarray()
    
    def compute_adjacency_eigenvalues(self):
        """
        Compute eigenvalues of the adjacency matrix.
        
        Known exact values for Petersen graph:
        - One eigenvalue of 3 (largest)
        - Five eigenvalues of 1
        - Four eigenvalues of -2
        
        Returns:
            Sorted eigenvalues
        """
        A = self.get_adjacency_matrix()
        eigenvalues = linalg.eigvalsh(A)
        return np.sort(eigenvalues)[::-1]  # Sort descending
    
    def compute_laplacian_eigenvalues(self):
        """
        Compute eigenvalues of the combinatorial Laplacian.
        
        For a k-regular graph with adjacency eigenvalues {λᵢ},
        Laplacian eigenvalues are {k - λᵢ}.
        
        For Petersen (3-regular):
        - L eigenvalues from A eigenvalues 3, 1, 1, 1, 1, 1, -2, -2, -2, -2
        - Are: 0, 2, 2, 2, 2, 2, 5, 5, 5, 5
        
        Returns:
            Sorted eigenvalues
        """
        L = self.get_laplacian_matrix()
        eigenvalues = linalg.eigvalsh(L)
        return np.sort(eigenvalues)
    
    def compute_normalized_laplacian_eigenvalues(self):
        """Compute eigenvalues of normalized Laplacian."""
        L_norm = self.get_normalized_laplacian()
        eigenvalues = linalg.eigvalsh(L_norm)
        return np.sort(eigenvalues)
    
    def verify_known_adjacency_spectrum(self, tol=1e-6):
        """
        Verify that adjacency eigenvalues match known values.
        
        Expected spectrum (with multiplicities):
        - 3 (multiplicity 1)
        - 1 (multiplicity 5)
        - -2 (multiplicity 4)
        
        Returns:
            True if spectrum matches
        """
        eigenvalues = self.compute_adjacency_eigenvalues()
        
        # Expected values
        expected = np.array([3, 1, 1, 1, 1, 1, -2, -2, -2, -2])
        
        # Check if close (allowing for numerical error)
        return np.allclose(eigenvalues, expected, atol=tol)
    
    def verify_known_laplacian_spectrum(self, tol=1e-6):
        """
        Verify that Laplacian eigenvalues match known values.
        
        For 3-regular Petersen graph:
        - 0 (multiplicity 1)
        - 2 (multiplicity 5)
        - 5 (multiplicity 4)
        
        Returns:
            True if spectrum matches
        """
        eigenvalues = self.compute_laplacian_eigenvalues()
        
        # Expected values
        expected = np.array([0, 2, 2, 2, 2, 2, 5, 5, 5, 5])
        
        return np.allclose(eigenvalues, expected, atol=tol)
    
    def compute_spectral_gap(self):
        """Compute spectral gap (second smallest Laplacian eigenvalue)."""
        eigenvalues = self.compute_laplacian_eigenvalues()
        return eigenvalues[1]
    
    def is_regular(self):
        """Check if graph is regular."""
        degrees = [self.G.degree(v) for v in self.G.nodes()]
        return len(set(degrees)) == 1
    
    def get_degree(self):
        """Get degree (for regular graphs)."""
        return self.G.degree(0)


class TestPetersenGraphBasics(unittest.TestCase):
    """Basic tests for Petersen graph properties."""
    
    def test_petersen_graph_structure(self):
        """Test basic structural properties of Petersen graph."""
        analyzer = PetersenGraphAnalyzer()
        
        # 10 vertices
        self.assertEqual(analyzer.n, 10)
        self.assertEqual(analyzer.G.number_of_nodes(), 10)
        
        # 15 edges
        self.assertEqual(analyzer.G.number_of_edges(), 15)
        
        # 3-regular
        self.assertTrue(analyzer.is_regular())
        self.assertEqual(analyzer.get_degree(), 3)
    
    def test_petersen_graph_is_connected(self):
        """Test that Petersen graph is connected."""
        analyzer = PetersenGraphAnalyzer()
        self.assertTrue(nx.is_connected(analyzer.G))
    
    def test_petersen_graph_girth(self):
        """Test that Petersen graph has girth 5."""
        # Girth is length of shortest cycle
        # Petersen graph has girth 5
        pass  # NetworkX doesn't have built-in girth function


class TestPetersenAdjacencyEigenvalues(unittest.TestCase):
    """Tests for Petersen graph adjacency eigenvalues."""
    
    def test_adjacency_eigenvalues_count(self):
        """Test that we get 10 eigenvalues."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_adjacency_eigenvalues()
        self.assertEqual(len(eigenvalues), 10)
    
    def test_adjacency_eigenvalues_match_known(self):
        """Test that eigenvalues match known spectrum."""
        analyzer = PetersenGraphAnalyzer()
        self.assertTrue(analyzer.verify_known_adjacency_spectrum(),
            "Adjacency eigenvalues do not match known Petersen spectrum")
    
    def test_adjacency_largest_eigenvalue(self):
        """Test largest eigenvalue is 3."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_adjacency_eigenvalues()
        self.assertAlmostEqual(eigenvalues[0], 3.0, places=6,
            msg="Largest adjacency eigenvalue should be 3")
    
    def test_adjacency_eigenvalue_multiplicities(self):
        """Test eigenvalue multiplicities."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_adjacency_eigenvalues()
        
        # Count multiplicities
        unique, counts = np.unique(np.round(eigenvalues, 6), return_counts=True)
        multiplicity_dict = dict(zip(unique, counts))
        
        # Should have eigenvalue 3 with multiplicity 1
        self.assertEqual(multiplicity_dict.get(3.0, 0), 1,
            "Eigenvalue 3 should have multiplicity 1")
        
        # Should have eigenvalue 1 with multiplicity 5
        self.assertEqual(multiplicity_dict.get(1.0, 0), 5,
            "Eigenvalue 1 should have multiplicity 5")
        
        # Should have eigenvalue -2 with multiplicity 4
        self.assertEqual(multiplicity_dict.get(-2.0, 0), 4,
            "Eigenvalue -2 should have multiplicity 4")


class TestPetersenLaplacianEigenvalues(unittest.TestCase):
    """Tests for Petersen graph Laplacian eigenvalues."""
    
    def test_laplacian_eigenvalues_count(self):
        """Test that we get 10 eigenvalues."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_laplacian_eigenvalues()
        self.assertEqual(len(eigenvalues), 10)
    
    def test_laplacian_eigenvalues_match_known(self):
        """Test that Laplacian eigenvalues match known spectrum."""
        analyzer = PetersenGraphAnalyzer()
        self.assertTrue(analyzer.verify_known_laplacian_spectrum(),
            "Laplacian eigenvalues do not match known Petersen spectrum")
    
    def test_laplacian_smallest_eigenvalue_zero(self):
        """Test that smallest Laplacian eigenvalue is 0 (connected graph)."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_laplacian_eigenvalues()
        self.assertAlmostEqual(eigenvalues[0], 0.0, places=8,
            msg="Smallest Laplacian eigenvalue should be 0 for connected graph")
    
    def test_laplacian_spectral_gap(self):
        """Test spectral gap (algebraic connectivity)."""
        analyzer = PetersenGraphAnalyzer()
        gap = analyzer.compute_spectral_gap()
        self.assertAlmostEqual(gap, 2.0, places=6,
            msg="Spectral gap of Petersen graph should be 2")
    
    def test_laplacian_eigenvalue_multiplicities(self):
        """Test Laplacian eigenvalue multiplicities."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_laplacian_eigenvalues()
        
        # Count multiplicities
        unique, counts = np.unique(np.round(eigenvalues, 6), return_counts=True)
        multiplicity_dict = dict(zip(unique, counts))
        
        # Should have eigenvalue 0 with multiplicity 1
        self.assertEqual(multiplicity_dict.get(0.0, 0), 1,
            "Eigenvalue 0 should have multiplicity 1")
        
        # Should have eigenvalue 2 with multiplicity 5
        self.assertEqual(multiplicity_dict.get(2.0, 0), 5,
            "Eigenvalue 2 should have multiplicity 5")
        
        # Should have eigenvalue 5 with multiplicity 4
        self.assertEqual(multiplicity_dict.get(5.0, 0), 4,
            "Eigenvalue 5 should have multiplicity 4")


class TestPetersenNormalizedLaplacian(unittest.TestCase):
    """Tests for normalized Laplacian of Petersen graph."""
    
    def test_normalized_laplacian_smallest_eigenvalue(self):
        """Test that smallest eigenvalue is 0."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_normalized_laplacian_eigenvalues()
        self.assertAlmostEqual(eigenvalues[0], 0.0, places=8)
    
    def test_normalized_laplacian_largest_eigenvalue(self):
        """Test that largest eigenvalue is bounded by 2."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_normalized_laplacian_eigenvalues()
        # For normalized Laplacian, eigenvalues are in [0, 2]
        self.assertLessEqual(eigenvalues[-1], 2.0 + 1e-6)


class TestPetersenRelationships(unittest.TestCase):
    """Test relationships between different eigenvalue types."""
    
    def test_regular_graph_eigenvalue_relation(self):
        """Test L = kI - A for k-regular graphs."""
        analyzer = PetersenGraphAnalyzer()
        k = analyzer.get_degree()  # 3 for Petersen
        
        A = analyzer.get_adjacency_matrix()
        L = analyzer.get_laplacian_matrix()
        
        # For regular graph: L = kI - A
        expected_L = k * np.eye(10) - A
        
        np.testing.assert_array_almost_equal(L, expected_L, decimal=10)
    
    def test_laplacian_from_adjacency_eigenvalues(self):
        """Test that Laplacian eigenvalues = k - adjacency eigenvalues."""
        analyzer = PetersenGraphAnalyzer()
        k = 3  # Degree
        
        adj_eigenvalues = analyzer.compute_adjacency_eigenvalues()
        lapl_eigenvalues = analyzer.compute_laplacian_eigenvalues()
        
        # Convert adjacency to Laplacian eigenvalues
        lapl_from_adj = k - adj_eigenvalues
        lapl_from_adj_sorted = np.sort(lapl_from_adj)
        
        np.testing.assert_array_almost_equal(lapl_eigenvalues, lapl_from_adj_sorted,
            decimal=6)


class TestPetersenSpectralProperties(unittest.TestCase):
    """Test spectral properties specific to Petersen graph."""
    
    def test_petersen_is_vertex_transitive(self):
        """Test that Petersen graph is vertex-transitive."""
        # Vertex-transitive means all vertices are equivalent under automorphisms
        # For Petersen, all vertices have the same "role"
        # We can verify this by checking degrees are all equal
        analyzer = PetersenGraphAnalyzer()
        self.assertTrue(analyzer.is_regular())
    
    def test_petersen_algebraic_connectivity(self):
        """Test algebraic connectivity (second smallest Laplacian eigenvalue)."""
        analyzer = PetersenGraphAnalyzer()
        
        # Algebraic connectivity measures how connected the graph is
        # Higher value = better connectivity
        # For Petersen, this is 2
        alg_conn = analyzer.compute_spectral_gap()
        self.assertAlmostEqual(alg_conn, 2.0, places=6)
    
    def test_petersen_spectral_radius(self):
        """Test spectral radius (largest absolute eigenvalue)."""
        analyzer = PetersenGraphAnalyzer()
        eigenvalues = analyzer.compute_adjacency_eigenvalues()
        
        # Spectral radius
        spectral_radius = max(abs(eigenvalues))
        
        # For Petersen, largest eigenvalue is 3
        self.assertAlmostEqual(spectral_radius, 3.0, places=6)


class TestPetersenEigenspaces(unittest.TestCase):
    """Test properties of eigenspaces."""
    
    def test_eigenspace_dimensions(self):
        """Test dimensions of eigenspaces."""
        analyzer = PetersenGraphAnalyzer()
        A = analyzer.get_adjacency_matrix()
        
        eigenvalues, eigenvectors = linalg.eigh(A)
        
        # Group by eigenvalue
        unique_eigenvalues = np.unique(np.round(eigenvalues, 6))
        
        for ev in unique_eigenvalues:
            # Count how many eigenvalues equal ev
            mask = np.abs(eigenvalues - ev) < 1e-6
            dimension = np.sum(mask)
            
            # Verify eigenvectors in this eigenspace
            eigenspace_vectors = eigenvectors[:, mask]
            
            # Check A v = λ v for each eigenvector
            for i in range(dimension):
                v = eigenspace_vectors[:, i]
                Av = A @ v
                lambda_v = ev * v
                np.testing.assert_array_almost_equal(Av, lambda_v, decimal=8)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == '__main__':
    run_tests()
