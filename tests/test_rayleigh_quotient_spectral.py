#!/usr/bin/env python3
"""
Tests for Rayleigh quotient and spectral decomposition formalization.

The Rayleigh quotient for a matrix A and vector x is:
    R(A, x) = (x^T A x) / (x^T x)

For symmetric matrices, the Rayleigh quotient has important properties:
- min R(A, x) = λ_min (smallest eigenvalue)
- max R(A, x) = λ_max (largest eigenvalue)
- Critical points are eigenvectors

For graph Laplacians, the Rayleigh quotient measures expansion.

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


class RayleighQuotientAnalyzer:
    """Analyzer for Rayleigh quotient and spectral decomposition."""
    
    def __init__(self, matrix):
        """
        Initialize with a symmetric matrix.
        
        Args:
            matrix: Symmetric matrix (numpy array)
        """
        self.A = np.array(matrix)
        assert self.A.shape[0] == self.A.shape[1], "Matrix must be square"
        # Check symmetry (up to numerical tolerance)
        assert np.allclose(self.A, self.A.T), "Matrix must be symmetric"
        self.n = self.A.shape[0]
        
    def rayleigh_quotient(self, x):
        """
        Compute Rayleigh quotient R(A, x) = (x^T A x) / (x^T x).
        
        Args:
            x: Vector (numpy array)
            
        Returns:
            Rayleigh quotient value
        """
        x = np.array(x)
        numerator = x.T @ self.A @ x
        denominator = x.T @ x
        
        if abs(denominator) < 1e-10:
            raise ValueError("Zero vector not allowed")
        
        return numerator / denominator
    
    def spectral_decomposition(self):
        """
        Compute spectral decomposition of the matrix.
        
        For symmetric A: A = Q Λ Q^T
        where Λ is diagonal matrix of eigenvalues,
        Q is orthogonal matrix of eigenvectors.
        
        Returns:
            Tuple (eigenvalues, eigenvectors)
            eigenvalues: sorted array of eigenvalues
            eigenvectors: matrix where column i is eigenvector for eigenvalue i
        """
        eigenvalues, eigenvectors = linalg.eigh(self.A)
        
        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        return eigenvalues, eigenvectors
    
    def verify_spectral_decomposition(self, tol=1e-10):
        """
        Verify that the spectral decomposition is correct.
        
        Checks:
        1. A = Q Λ Q^T
        2. Q^T Q = I (orthogonality)
        3. Each column of Q is an eigenvector
        
        Returns:
            True if verification passes
        """
        eigenvalues, Q = self.spectral_decomposition()
        Lambda = np.diag(eigenvalues)
        
        # Check 1: A = Q Λ Q^T
        reconstructed = Q @ Lambda @ Q.T
        if not np.allclose(self.A, reconstructed, atol=tol):
            return False
        
        # Check 2: Q^T Q = I
        identity = Q.T @ Q
        if not np.allclose(identity, np.eye(self.n), atol=tol):
            return False
        
        # Check 3: A Q = Q Λ (each column is eigenvector)
        if not np.allclose(self.A @ Q, Q @ Lambda, atol=tol):
            return False
        
        return True
    
    def rayleigh_quotient_at_eigenvector(self, index):
        """
        Compute Rayleigh quotient at a specific eigenvector.
        
        Should return the corresponding eigenvalue.
        
        Args:
            index: Index of eigenvector (0 = smallest eigenvalue)
            
        Returns:
            Rayleigh quotient value (should equal eigenvalue)
        """
        eigenvalues, eigenvectors = self.spectral_decomposition()
        x = eigenvectors[:, index]
        return self.rayleigh_quotient(x)
    
    def min_max_rayleigh_quotient(self, num_random=1000):
        """
        Estimate min and max of Rayleigh quotient over random vectors.
        
        The minimum should approach λ_min and maximum should approach λ_max.
        
        Args:
            num_random: Number of random vectors to try
            
        Returns:
            Tuple (min_R, max_R)
        """
        eigenvalues, _ = self.spectral_decomposition()
        
        min_R = float('inf')
        max_R = float('-inf')
        
        for _ in range(num_random):
            # Random unit vector
            x = np.random.randn(self.n)
            x = x / np.linalg.norm(x)
            
            R = self.rayleigh_quotient(x)
            min_R = min(min_R, R)
            max_R = max(max_R, R)
        
        return min_R, max_R


class TestRayleighQuotientBasics(unittest.TestCase):
    """Basic tests for Rayleigh quotient."""
    
    def test_rayleigh_quotient_identity_matrix(self):
        """Test Rayleigh quotient on identity matrix."""
        A = np.eye(5)
        analyzer = RayleighQuotientAnalyzer(A)
        
        # For identity matrix, R(I, x) = 1 for any x
        x = np.random.randn(5)
        R = analyzer.rayleigh_quotient(x)
        self.assertAlmostEqual(R, 1.0, places=10)
    
    def test_rayleigh_quotient_diagonal_matrix(self):
        """Test Rayleigh quotient on diagonal matrix."""
        # Diagonal matrix with entries [1, 2, 3, 4, 5]
        A = np.diag([1, 2, 3, 4, 5])
        analyzer = RayleighQuotientAnalyzer(A)
        
        # Standard basis vector e_i gives R = diagonal entry i
        for i in range(5):
            e_i = np.zeros(5)
            e_i[i] = 1
            R = analyzer.rayleigh_quotient(e_i)
            self.assertAlmostEqual(R, i + 1, places=10)
    
    def test_rayleigh_quotient_at_eigenvector(self):
        """Test that Rayleigh quotient at eigenvector equals eigenvalue."""
        A = np.array([[4, 1, 0],
                      [1, 3, 1],
                      [0, 1, 2]])
        analyzer = RayleighQuotientAnalyzer(A)
        eigenvalues, _ = analyzer.spectral_decomposition()
        
        # Check each eigenvector
        for i in range(3):
            R = analyzer.rayleigh_quotient_at_eigenvector(i)
            self.assertAlmostEqual(R, eigenvalues[i], places=8,
                msg=f"Rayleigh quotient at eigenvector {i} should equal eigenvalue")


class TestSpectralDecomposition(unittest.TestCase):
    """Tests for spectral decomposition."""
    
    def test_spectral_decomposition_identity(self):
        """Test spectral decomposition of identity matrix."""
        A = np.eye(4)
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, eigenvectors = analyzer.spectral_decomposition()
        
        # Identity has all eigenvalues = 1
        expected_eigenvalues = np.ones(4)
        np.testing.assert_array_almost_equal(eigenvalues, expected_eigenvalues)
        
        # Verify decomposition
        self.assertTrue(analyzer.verify_spectral_decomposition())
    
    def test_spectral_decomposition_diagonal(self):
        """Test spectral decomposition of diagonal matrix."""
        diag_entries = [5, 3, 7, 1, 9]
        A = np.diag(diag_entries)
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, eigenvectors = analyzer.spectral_decomposition()
        
        # Eigenvalues should be diagonal entries (sorted)
        expected_eigenvalues = np.sort(diag_entries)
        np.testing.assert_array_almost_equal(eigenvalues, expected_eigenvalues)
        
        # Verify decomposition
        self.assertTrue(analyzer.verify_spectral_decomposition())
    
    def test_spectral_decomposition_symmetric(self):
        """Test spectral decomposition of general symmetric matrix."""
        A = np.array([[4, 1, 2],
                      [1, 5, 1],
                      [2, 1, 6]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        # Verify decomposition properties
        self.assertTrue(analyzer.verify_spectral_decomposition())
    
    def test_orthogonality_of_eigenvectors(self):
        """Test that eigenvectors are orthogonal."""
        A = np.random.randn(5, 5)
        A = (A + A.T) / 2  # Make symmetric
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, Q = analyzer.spectral_decomposition()
        
        # Q^T Q should be identity
        identity = Q.T @ Q
        np.testing.assert_array_almost_equal(identity, np.eye(5), decimal=10)


class TestRayleighQuotientBounds(unittest.TestCase):
    """Test bounds on Rayleigh quotient."""
    
    def test_rayleigh_bounds_random_symmetric(self):
        """Test that Rayleigh quotient is bounded by eigenvalues."""
        # Create random symmetric matrix
        A = np.random.randn(6, 6)
        A = (A + A.T) / 2
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, _ = analyzer.spectral_decomposition()
        lambda_min = eigenvalues[0]
        lambda_max = eigenvalues[-1]
        
        # Try many random vectors
        for _ in range(100):
            x = np.random.randn(6)
            R = analyzer.rayleigh_quotient(x)
            
            # R should be bounded by eigenvalues
            self.assertGreaterEqual(R, lambda_min - 1e-10,
                "Rayleigh quotient should be >= minimum eigenvalue")
            self.assertLessEqual(R, lambda_max + 1e-10,
                "Rayleigh quotient should be <= maximum eigenvalue")
    
    def test_rayleigh_achieves_bounds(self):
        """Test that Rayleigh quotient achieves min/max at eigenvectors."""
        A = np.array([[5, 1, 0],
                      [1, 4, 1],
                      [0, 1, 3]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, eigenvectors = analyzer.spectral_decomposition()
        
        # At minimum eigenvector
        x_min = eigenvectors[:, 0]
        R_min = analyzer.rayleigh_quotient(x_min)
        self.assertAlmostEqual(R_min, eigenvalues[0], places=10)
        
        # At maximum eigenvector
        x_max = eigenvectors[:, -1]
        R_max = analyzer.rayleigh_quotient(x_max)
        self.assertAlmostEqual(R_max, eigenvalues[-1], places=10)


class TestRayleighQuotientForGraphLaplacian(unittest.TestCase):
    """Test Rayleigh quotient for graph Laplacians."""
    
    def test_laplacian_path_graph(self):
        """Test Rayleigh quotient for path graph Laplacian."""
        G = nx.path_graph(10)
        L = nx.normalized_laplacian_matrix(G).toarray()
        
        analyzer = RayleighQuotientAnalyzer(L)
        
        # Verify spectral decomposition
        self.assertTrue(analyzer.verify_spectral_decomposition())
        
        # Smallest eigenvalue should be 0 (connected graph)
        eigenvalues, _ = analyzer.spectral_decomposition()
        self.assertAlmostEqual(eigenvalues[0], 0.0, places=8)
    
    def test_laplacian_cycle_graph(self):
        """Test Rayleigh quotient for cycle graph Laplacian."""
        G = nx.cycle_graph(12)
        L = nx.normalized_laplacian_matrix(G).toarray()
        
        analyzer = RayleighQuotientAnalyzer(L)
        
        # Verify spectral decomposition
        self.assertTrue(analyzer.verify_spectral_decomposition())
        
        eigenvalues, _ = analyzer.spectral_decomposition()
        # Smallest eigenvalue = 0
        self.assertAlmostEqual(eigenvalues[0], 0.0, places=8)
        
        # Second eigenvalue (spectral gap) should match known formula
        # For cycle: λ₁ = 1 - cos(2π/n)
        expected_gap = 1 - np.cos(2 * np.pi / 12)
        self.assertAlmostEqual(eigenvalues[1], expected_gap, places=6)
    
    def test_laplacian_complete_graph(self):
        """Test Rayleigh quotient for complete graph Laplacian."""
        n = 8
        G = nx.complete_graph(n)
        L = nx.normalized_laplacian_matrix(G).toarray()
        
        analyzer = RayleighQuotientAnalyzer(L)
        
        eigenvalues, _ = analyzer.spectral_decomposition()
        
        # First eigenvalue = 0
        self.assertAlmostEqual(eigenvalues[0], 0.0, places=8)
        
        # All other eigenvalues = n/(n-1) for complete graph
        expected = n / (n - 1)
        for i in range(1, n):
            self.assertAlmostEqual(eigenvalues[i], expected, places=6)


class TestRayleighQuotientVariationalPrinciple(unittest.TestCase):
    """Test variational characterization of eigenvalues via Rayleigh quotient."""
    
    def test_min_rayleigh_is_min_eigenvalue(self):
        """Test that min Rayleigh quotient equals minimum eigenvalue."""
        A = np.array([[3, 1, 0],
                      [1, 2, 1],
                      [0, 1, 4]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, _ = analyzer.spectral_decomposition()
        lambda_min = eigenvalues[0]
        
        # Estimate minimum via random sampling
        min_R, _ = analyzer.min_max_rayleigh_quotient(num_random=2000)
        
        # Should be close to minimum eigenvalue
        self.assertAlmostEqual(min_R, lambda_min, places=2)
    
    def test_max_rayleigh_is_max_eigenvalue(self):
        """Test that max Rayleigh quotient equals maximum eigenvalue."""
        A = np.array([[3, 1, 0],
                      [1, 2, 1],
                      [0, 1, 4]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, _ = analyzer.spectral_decomposition()
        lambda_max = eigenvalues[-1]
        
        # Estimate maximum via random sampling
        _, max_R = analyzer.min_max_rayleigh_quotient(num_random=2000)
        
        # Should be close to maximum eigenvalue
        self.assertAlmostEqual(max_R, lambda_max, places=2)


class TestSpectralDecompositionReconstruction(unittest.TestCase):
    """Test matrix reconstruction from spectral decomposition."""
    
    def test_reconstruction_from_decomposition(self):
        """Test that A = Q Λ Q^T reconstructs the original matrix."""
        A = np.array([[6, 2, 1],
                      [2, 5, 2],
                      [1, 2, 4]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, Q = analyzer.spectral_decomposition()
        Lambda = np.diag(eigenvalues)
        
        # Reconstruct A
        A_reconstructed = Q @ Lambda @ Q.T
        
        np.testing.assert_array_almost_equal(A, A_reconstructed, decimal=10)
    
    def test_low_rank_approximation(self):
        """Test low-rank approximation using largest eigenvalues."""
        # Create a matrix
        A = np.array([[5, 2, 1, 0],
                      [2, 4, 1, 0],
                      [1, 1, 3, 0],
                      [0, 0, 0, 1]])
        analyzer = RayleighQuotientAnalyzer(A)
        
        eigenvalues, Q = analyzer.spectral_decomposition()
        
        # Rank-2 approximation (keep 2 largest eigenvalues)
        Lambda_approx = np.diag(eigenvalues[-2:])
        Q_approx = Q[:, -2:]
        
        A_approx = Q_approx @ Lambda_approx @ Q_approx.T
        
        # Approximation should be different but close-ish
        self.assertFalse(np.allclose(A, A_approx))
        
        # But should preserve largest eigenvalues
        eigenvalues_approx, _ = RayleighQuotientAnalyzer(A_approx).spectral_decomposition()
        # The two largest should match
        self.assertAlmostEqual(eigenvalues_approx[-1], eigenvalues[-1], places=6)
        self.assertAlmostEqual(eigenvalues_approx[-2], eigenvalues[-2], places=6)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == '__main__':
    run_tests()
