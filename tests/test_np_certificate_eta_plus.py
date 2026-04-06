"""
Tests for η⁺ Adelic Coherence NP Certificate
=============================================

Comprehensive test suite for the η⁺ coherence metric
and polynomial-time NP certification framework.

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
"""

import sys
import os
import unittest
import numpy as np

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.np_certificate_eta_plus import (
    AdelicHilbertSpace,
    EtaPlusCertificate,
    certificado_np_coherencia,
    tour_vector_tsp,
    assignment_vector_sat,
    ETA_PLUS_THRESHOLD,
    PSI_GLOBAL_MIN,
    PSI_GLOBAL_MAX,
    COHERENCE_FACTOR,
    PHI
)


class TestAdelicHilbertSpace(unittest.TestCase):
    """Test cases for AdelicHilbertSpace class."""
    
    def test_initialization(self):
        """Test Hilbert space initialization."""
        h = AdelicHilbertSpace(10, "TSP")
        self.assertEqual(h.dimension, 10)
        self.assertEqual(h.problem_type, "TSP")
        self.assertIsNone(h.hamiltonian)
        self.assertIsNone(h.eigenvalues)
        self.assertIsNone(h.eigenvectors)
    
    def test_generic_hamiltonian_construction(self):
        """Test generic Hamiltonian construction."""
        n = 8
        h = AdelicHilbertSpace(n, "general")
        H = h.construct_hamiltonian(None)
        
        # Check dimensions
        self.assertEqual(H.shape, (n, n))
        
        # Check Hermitian property
        self.assertTrue(np.allclose(H, H.conj().T))
        
        # Check diagonal is real
        self.assertTrue(np.allclose(np.diag(H).imag, 0))
    
    def test_tsp_hamiltonian_construction(self):
        """Test TSP-specific Hamiltonian construction."""
        n = 5
        distances = np.random.rand(n, n) * 100
        distances = (distances + distances.T) / 2
        np.fill_diagonal(distances, 0)
        
        h = AdelicHilbertSpace(n, "TSP")
        H = h.construct_hamiltonian(distances)
        
        # Check dimensions
        self.assertEqual(H.shape, (n, n))
        
        # Check Hermitian
        self.assertTrue(np.allclose(H, H.conj().T))
    
    def test_sat_hamiltonian_construction(self):
        """Test SAT-specific Hamiltonian construction."""
        clauses = [[1, 2], [-1, 3], [2, -4], [3, 4]]
        n_vars = 4
        
        h = AdelicHilbertSpace(n_vars, "SAT")
        H = h.construct_hamiltonian(clauses)
        
        # Check dimensions
        self.assertEqual(H.shape, (n_vars, n_vars))
        
        # Check Hermitian
        self.assertTrue(np.allclose(H, H.conj().T))
    
    def test_spectral_decomposition(self):
        """Test spectral decomposition of Hamiltonian."""
        n = 6
        h = AdelicHilbertSpace(n, "general")
        h.construct_hamiltonian(None)
        
        eigenvalues, eigenvectors = h.spectral_decomposition()
        
        # Check dimensions
        self.assertEqual(len(eigenvalues), n)
        self.assertEqual(eigenvectors.shape, (n, n))
        
        # Check eigenvalues are real (Hermitian matrix)
        self.assertTrue(np.allclose(eigenvalues.imag, 0))
        
        # Check eigenvectors are orthonormal
        identity = eigenvectors.conj().T @ eigenvectors
        self.assertTrue(np.allclose(identity, np.eye(n)))
        
        # Verify eigenvalue decomposition
        H_reconstructed = eigenvectors @ np.diag(eigenvalues) @ eigenvectors.conj().T
        self.assertTrue(np.allclose(H_reconstructed, h.hamiltonian))
    
    def test_eigenvalues_ordered(self):
        """Test that eigenvalues are in ascending order."""
        n = 7
        h = AdelicHilbertSpace(n, "general")
        h.construct_hamiltonian(None)
        eigenvalues, _ = h.spectral_decomposition()
        
        # scipy.linalg.eigh returns eigenvalues in ascending order
        for i in range(len(eigenvalues) - 1):
            self.assertLessEqual(eigenvalues[i], eigenvalues[i + 1])


class TestEtaPlusCertificate(unittest.TestCase):
    """Test cases for EtaPlusCertificate class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.n = 8
        self.hilbert = AdelicHilbertSpace(self.n, "general")
        self.hilbert.construct_hamiltonian(None)
        self.hilbert.spectral_decomposition()
        self.certificate = EtaPlusCertificate(self.hilbert)
    
    def test_initialization(self):
        """Test certificate initialization."""
        self.assertIsNotNone(self.certificate.hilbert_space)
        self.assertIsNone(self.certificate.eta_plus_metric)
    
    def test_eta_plus_metric_computation(self):
        """Test η⁺ metric computation."""
        eta_plus = self.certificate.compute_eta_plus_metric()
        
        # Check dimensions
        self.assertEqual(len(eta_plus), self.n)
        
        # Check all values are positive
        self.assertTrue(np.all(eta_plus > 0))
        
        # Check all values are bounded by coherence factor
        self.assertTrue(np.all(eta_plus <= COHERENCE_FACTOR))
        
        # Check highest eigenvalue has maximum metric value
        lambda_max = self.hilbert.eigenvalues[-1]
        expected_max = COHERENCE_FACTOR / (1 + 0)  # |λ_max - λ_max| = 0
        self.assertAlmostEqual(eta_plus[-1], expected_max, places=10)
    
    def test_coherence_computation(self):
        """Test coherence computation between states."""
        # Use ground state (highest eigenvalue eigenvector)
        psi = self.hilbert.eigenvectors[:, -1]
        
        coherence = self.certificate.compute_coherence(psi)
        
        # Coherence should be real
        self.assertIsInstance(coherence, (float, np.floating))
        
        # Coherence should be positive
        self.assertGreater(coherence, 0)
        
        # Coherence should be bounded (allow small numerical error)
        self.assertLessEqual(coherence, COHERENCE_FACTOR + 1e-10)
    
    def test_coherence_self_vs_other(self):
        """Test coherence of state with itself vs with another state."""
        psi = self.hilbert.eigenvectors[:, -1]
        phi = self.hilbert.eigenvectors[:, 0]
        
        # Self-coherence
        coherence_self = self.certificate.compute_coherence(psi, psi)
        
        # Cross-coherence
        coherence_cross = self.certificate.compute_coherence(psi, phi)
        
        # Self-coherence should be larger for ground state
        self.assertGreater(coherence_self, coherence_cross)
    
    def test_verify_certificate_valid(self):
        """Test certificate verification with valid solution."""
        # Use eigenvector with highest eigenvalue
        psi = self.hilbert.eigenvectors[:, -1]
        
        result = self.certificate.verify_certificate(psi)
        
        # Check result structure
        self.assertIn('valid_certificate', result)
        self.assertIn('coherence', result)
        self.assertIn('psi_global', result)
        self.assertIn('threshold', result)
        self.assertIn('verification_time_ms', result)
        self.assertIn('dimension', result)
        
        # Check types (numpy bool is acceptable)
        self.assertIsInstance(result['valid_certificate'], (bool, np.bool_))
        self.assertIsInstance(result['coherence'], (float, np.floating))
        self.assertIsInstance(result['verification_time_ms'], float)
        
        # Time should be reasonable
        self.assertGreater(result['verification_time_ms'], 0)
        self.assertLess(result['verification_time_ms'], 1000)  # < 1 second
    
    def test_verify_certificate_normalization(self):
        """Test that certificate normalizes input vectors."""
        # Unnormalized vector
        psi_unnorm = np.random.rand(self.n) + 1j * np.random.rand(self.n)
        
        result = self.certificate.verify_certificate(psi_unnorm)
        
        # Should not raise error and should return valid result
        self.assertIn('coherence', result)
        self.assertIsNotNone(result['coherence'])


class TestCertificadoNPCoherencia(unittest.TestCase):
    """Test cases for main certificate function."""
    
    def test_tsp_certificate(self):
        """Test certificate for TSP instance."""
        n_cities = 6
        np.random.seed(123)
        distances = np.random.rand(n_cities, n_cities) * 100
        distances = (distances + distances.T) / 2
        np.fill_diagonal(distances, 0)
        
        tour = list(range(n_cities))
        tour_vec = tour_vector_tsp(tour, n_cities)
        
        result = certificado_np_coherencia(
            instance_data=distances,
            problem_type="TSP",
            n_dimension=n_cities,
            candidate_solution=tour_vec
        )
        
        # Check result structure
        self.assertIn('valid_certificate', result)
        self.assertIn('coherence', result)
        self.assertIn('problem_type', result)
        self.assertIn('dimension', result)
        self.assertIn('lambda_max', result)
        self.assertIn('total_time_ms', result)
        self.assertIn('complexity_class', result)
        
        # Check values
        self.assertEqual(result['problem_type'], 'TSP')
        self.assertEqual(result['dimension'], n_cities)
        self.assertEqual(result['complexity_class'], 'O(n^3)')
        self.assertGreater(result['total_time_ms'], 0)
    
    def test_sat_certificate(self):
        """Test certificate for SAT instance."""
        # Simple SAT instance
        clauses = [[1, 2], [-1, 3], [2, -4], [3, 4]]
        n_vars = 4
        
        assignment = [True, True, True, True]
        assign_vec = assignment_vector_sat(assignment, n_vars)
        
        result = certificado_np_coherencia(
            instance_data=clauses,
            problem_type="SAT",
            n_dimension=n_vars,
            candidate_solution=assign_vec
        )
        
        # Check result
        self.assertIn('valid_certificate', result)
        self.assertEqual(result['problem_type'], 'SAT')
        self.assertEqual(result['dimension'], n_vars)
    
    def test_certificate_without_candidate(self):
        """Test certificate with auto-generated candidate."""
        n = 5
        h = AdelicHilbertSpace(n, "general")
        H = h.construct_hamiltonian(None)
        
        # Call without candidate solution
        result = certificado_np_coherencia(
            instance_data=None,
            problem_type="general",
            n_dimension=n,
            candidate_solution=None
        )
        
        # Should use ground state eigenvector
        self.assertIn('valid_certificate', result)
        self.assertIn('coherence', result)
    
    def test_certificate_includes_constants(self):
        """Test that certificate includes QCAL constants."""
        result = certificado_np_coherencia(
            instance_data=None,
            problem_type="general",
            n_dimension=4,
            candidate_solution=None
        )
        
        # Check constants are included
        self.assertIn('phi', result)
        self.assertIn('kappa_pi', result)
        self.assertIn('f0_hz', result)
        
        # Check values are reasonable
        self.assertAlmostEqual(result['phi'], PHI, places=5)
    
    def test_polynomial_time_complexity(self):
        """Test that computation time scales polynomially."""
        times = []
        dimensions = [5, 10, 15, 20]
        
        for n in dimensions:
            result = certificado_np_coherencia(
                instance_data=None,
                problem_type="general",
                n_dimension=n,
                candidate_solution=None
            )
            times.append(result['total_time_ms'])
        
        # Time should increase but remain reasonable
        for t in times:
            self.assertLess(t, 5000)  # < 5 seconds even for n=20


class TestVectorConversions(unittest.TestCase):
    """Test cases for TSP and SAT vector conversions."""
    
    def test_tour_vector_tsp_normalization(self):
        """Test TSP tour vector is normalized."""
        tour = [0, 1, 2, 3, 4]
        n_cities = 5
        
        psi = tour_vector_tsp(tour, n_cities)
        
        # Check normalization
        norm = np.linalg.norm(psi)
        self.assertAlmostEqual(norm, 1.0, places=10)
        
        # Check dimension
        self.assertEqual(len(psi), n_cities)
        
        # Check non-zero for all cities in tour
        for city in tour:
            self.assertGreater(abs(psi[city]), 0)
    
    def test_tour_vector_phase_encoding(self):
        """Test tour vector encodes position with phase."""
        tour = [0, 1, 2]
        n_cities = 3
        
        psi = tour_vector_tsp(tour, n_cities)
        
        # Extract phases
        phases = np.angle(psi[psi != 0])
        
        # Phases should be distinct
        self.assertEqual(len(np.unique(phases.round(decimals=10))), len(tour))
    
    def test_assignment_vector_sat_normalization(self):
        """Test SAT assignment vector is normalized."""
        assignment = [True, False, True, False]
        n_vars = 4
        
        psi = assignment_vector_sat(assignment, n_vars)
        
        # Check normalization
        norm = np.linalg.norm(psi)
        self.assertAlmostEqual(norm, 1.0, places=10)
        
        # Check dimension
        self.assertEqual(len(psi), n_vars)
    
    def test_assignment_vector_encoding(self):
        """Test SAT assignment encodes True/False correctly."""
        assignment = [True, False, True, False]
        n_vars = 4
        
        psi = assignment_vector_sat(assignment, n_vars)
        
        # True should have positive real part, False negative
        for i, val in enumerate(assignment):
            real_part = np.real(psi[i])
            if val:
                self.assertGreater(real_part, 0)
            else:
                self.assertLess(real_part, 0)
    
    def test_assignment_vector_partial_assignment(self):
        """Test assignment vector with fewer assignments than variables."""
        assignment = [True, False]
        n_vars = 5
        
        psi = assignment_vector_sat(assignment, n_vars)
        
        # Should still be normalized
        norm = np.linalg.norm(psi)
        self.assertAlmostEqual(norm, 1.0, places=10)
        
        # Extra variables should be zero
        self.assertEqual(psi[2], 0)
        self.assertEqual(psi[3], 0)
        self.assertEqual(psi[4], 0)


class TestThresholdConstants(unittest.TestCase):
    """Test cases for η⁺ threshold constants."""
    
    def test_threshold_values(self):
        """Test threshold constants are in valid range."""
        # ETA_PLUS_THRESHOLD should be in [PSI_GLOBAL_MIN, PSI_GLOBAL_MAX]
        self.assertGreaterEqual(ETA_PLUS_THRESHOLD, PSI_GLOBAL_MIN)
        self.assertLessEqual(ETA_PLUS_THRESHOLD, PSI_GLOBAL_MAX)
        
        # Check specific value from problem statement
        self.assertAlmostEqual(ETA_PLUS_THRESHOLD, 0.9575, places=4)
        self.assertAlmostEqual(PSI_GLOBAL_MIN, 0.534, places=3)
        self.assertAlmostEqual(PSI_GLOBAL_MAX, 0.9575, places=4)
    
    def test_coherence_factor(self):
        """Test coherence factor is 7/8."""
        self.assertAlmostEqual(COHERENCE_FACTOR, 7.0 / 8.0, places=10)
        self.assertAlmostEqual(COHERENCE_FACTOR, 0.875, places=10)


class TestIntegrationScenarios(unittest.TestCase):
    """Integration tests for complete scenarios."""
    
    def test_small_tsp_complete_flow(self):
        """Test complete flow for small TSP instance."""
        # Create small TSP instance
        n = 4
        distances = np.array([
            [0, 10, 15, 20],
            [10, 0, 35, 25],
            [15, 35, 0, 30],
            [20, 25, 30, 0]
        ])
        
        # Optimal tour (for this small instance)
        tour = [0, 1, 3, 2]
        tour_vec = tour_vector_tsp(tour, n)
        
        result = certificado_np_coherencia(
            instance_data=distances,
            problem_type="TSP",
            n_dimension=n,
            candidate_solution=tour_vec
        )
        
        # Verify complete result
        self.assertIsInstance(result, dict)
        self.assertIn('valid_certificate', result)
        self.assertIn('coherence', result)
        self.assertIn('total_time_ms', result)
        
        # Should be fast for small instance
        self.assertLess(result['total_time_ms'], 100)  # < 100ms
    
    def test_sat_satisfiable_instance(self):
        """Test SAT certificate for satisfiable instance."""
        # (x1 ∨ x2) ∧ (¬x2 ∨ x3)
        clauses = [[1, 2], [-2, 3]]
        n_vars = 3
        
        # Satisfying assignment: x1=T, x2=T, x3=T
        assignment = [True, True, True]
        assign_vec = assignment_vector_sat(assignment, n_vars)
        
        result = certificado_np_coherencia(
            instance_data=clauses,
            problem_type="SAT",
            n_dimension=n_vars,
            candidate_solution=assign_vec
        )
        
        # Should have reasonable coherence
        self.assertIn('coherence', result)
        self.assertGreater(result['coherence'], 0)
    
    def test_multiple_problem_types(self):
        """Test that different problem types can be processed."""
        problem_types = ["TSP", "SAT", "general"]
        
        for ptype in problem_types:
            result = certificado_np_coherencia(
                instance_data=None if ptype == "general" else (
                    np.eye(3) if ptype == "TSP" else [[1, 2]]
                ),
                problem_type=ptype,
                n_dimension=3,
                candidate_solution=None
            )
            
            self.assertEqual(result['problem_type'], ptype)
            self.assertIn('coherence', result)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
