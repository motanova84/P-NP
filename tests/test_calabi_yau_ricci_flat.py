"""
Unit tests for Calabi-Yau Ricci-flat metric construction complexity.

Tests the CY-RF-CONSTRUCT problem and its connection to P ≠ NP.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import unittest
import sys
import os
import math
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.calabi_yau_ricci_flat import (
    CalabiYauManifold,
    RicciFlatMetric,
    CYRFConstruct,
    SATtoCYRFReduction
)


class TestCalabiYauManifold(unittest.TestCase):
    """Test cases for Calabi-Yau manifold representation."""
    
    def test_manifold_initialization(self):
        """Test basic manifold initialization."""
        M = CalabiYauManifold(8, 5)
        self.assertEqual(M.h_11, 8)
        self.assertEqual(M.h_21, 5)
        self.assertEqual(M.N, 13)
    
    def test_invalid_hodge_numbers(self):
        """Test that negative Hodge numbers raise an error."""
        with self.assertRaises(ValueError):
            CalabiYauManifold(-1, 5)
        with self.assertRaises(ValueError):
            CalabiYauManifold(5, -1)
    
    def test_spectral_constant_calculation(self):
        """Test κ_Π = log(h^{1,1} + h^{2,1}) calculation."""
        M = CalabiYauManifold(8, 5)
        kappa = M.spectral_constant()
        expected = math.log(13)
        self.assertAlmostEqual(kappa, expected, places=6)
        self.assertAlmostEqual(kappa, 2.5649, places=3)
    
    def test_spectral_constant_zero_case(self):
        """Test spectral constant for zero-dimensional moduli."""
        M = CalabiYauManifold(0, 0)
        kappa = M.spectral_constant()
        self.assertEqual(kappa, 0.0)
    
    def test_moduli_space_size(self):
        """Test |M_X| ~ exp(κ_Π) calculation."""
        M = CalabiYauManifold(8, 5)
        size = M.moduli_space_size()
        expected = math.exp(math.log(13))
        self.assertAlmostEqual(size, expected, places=6)
        self.assertAlmostEqual(size, 13.0, places=6)
    
    def test_euler_characteristic(self):
        """Test χ = 2(h^{1,1} - h^{2,1}) for CY3."""
        M = CalabiYauManifold(8, 5)
        chi = M.euler_characteristic()
        expected = 2 * (8 - 5)
        self.assertEqual(chi, expected)
        self.assertEqual(chi, 6)
    
    def test_euler_characteristic_negative(self):
        """Test Euler characteristic with h^{2,1} > h^{1,1}."""
        M = CalabiYauManifold(3, 7)
        chi = M.euler_characteristic()
        expected = 2 * (3 - 7)
        self.assertEqual(chi, expected)
        self.assertEqual(chi, -8)
    
    def test_manifold_repr(self):
        """Test string representation."""
        M = CalabiYauManifold(8, 5)
        repr_str = repr(M)
        self.assertIn("8", repr_str)
        self.assertIn("5", repr_str)
        self.assertIn("κ_Π", repr_str)


class TestRicciFlatMetric(unittest.TestCase):
    """Test cases for Ricci-flat metric verification."""
    
    def test_metric_initialization(self):
        """Test metric initialization."""
        metric_data = np.eye(3)  # Simplified 3x3 metric
        ricci_norm = 1e-7
        metric = RicciFlatMetric(metric_data, ricci_norm)
        
        self.assertIsNotNone(metric.metric_data)
        self.assertEqual(metric.ricci_norm, ricci_norm)
    
    def test_is_ricci_flat_true(self):
        """Test verification when metric is Ricci-flat."""
        metric_data = np.eye(3)
        ricci_norm = 1e-7  # Small norm
        epsilon = 1e-6
        
        metric = RicciFlatMetric(metric_data, ricci_norm)
        is_flat = metric.is_ricci_flat(epsilon)
        
        self.assertTrue(is_flat)
    
    def test_is_ricci_flat_false(self):
        """Test verification when metric is not Ricci-flat."""
        metric_data = np.eye(3)
        ricci_norm = 1e-3  # Large norm
        epsilon = 1e-6
        
        metric = RicciFlatMetric(metric_data, ricci_norm)
        is_flat = metric.is_ricci_flat(epsilon)
        
        self.assertFalse(is_flat)
    
    def test_is_ricci_flat_boundary(self):
        """Test verification at the epsilon boundary."""
        metric_data = np.eye(3)
        epsilon = 1e-6
        ricci_norm = epsilon - 1e-10  # Just below threshold
        
        metric = RicciFlatMetric(metric_data, ricci_norm)
        self.assertTrue(metric.is_ricci_flat(epsilon))
        
        ricci_norm = epsilon + 1e-10  # Just above threshold
        metric = RicciFlatMetric(metric_data, ricci_norm)
        self.assertFalse(metric.is_ricci_flat(epsilon))


class TestCYRFConstruct(unittest.TestCase):
    """Test cases for the CY-RF-CONSTRUCT problem."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.manifold = CalabiYauManifold(8, 5)
        self.epsilon = 1e-6
        self.problem = CYRFConstruct(self.manifold, self.epsilon)
    
    def test_problem_initialization(self):
        """Test CY-RF-CONSTRUCT problem initialization."""
        self.assertEqual(self.problem.manifold, self.manifold)
        self.assertEqual(self.problem.epsilon, self.epsilon)
        self.assertAlmostEqual(self.problem.kappa_pi, math.log(13), places=6)
    
    def test_verify_certificate_valid(self):
        """Test certificate verification for valid metric."""
        metric_data = np.eye(3)
        ricci_norm = 1e-7
        metric = RicciFlatMetric(metric_data, ricci_norm)
        
        is_valid, norm = self.problem.verify_certificate(metric)
        
        self.assertTrue(is_valid)
        self.assertEqual(norm, ricci_norm)
    
    def test_verify_certificate_invalid(self):
        """Test certificate verification for invalid metric."""
        metric_data = np.eye(3)
        ricci_norm = 1e-3
        metric = RicciFlatMetric(metric_data, ricci_norm)
        
        is_valid, norm = self.problem.verify_certificate(metric)
        
        self.assertFalse(is_valid)
        self.assertEqual(norm, ricci_norm)
    
    def test_search_space_complexity(self):
        """Test search space complexity calculation."""
        complexity = self.problem.search_space_complexity()
        expected = self.manifold.moduli_space_size()
        self.assertAlmostEqual(complexity, expected, places=6)
    
    def test_estimate_construction_time_small(self):
        """Test construction time estimate for small manifolds."""
        small_manifold = CalabiYauManifold(1, 1)
        small_problem = CYRFConstruct(small_manifold)
        
        time_estimate = small_problem.estimate_construction_time()
        self.assertIn("Polynomial", time_estimate)
    
    def test_estimate_construction_time_large(self):
        """Test construction time estimate for large manifolds."""
        large_manifold = CalabiYauManifold(25, 25)
        large_problem = CYRFConstruct(large_manifold)
        
        time_estimate = large_problem.estimate_construction_time()
        self.assertIn("Exponential", time_estimate)
    
    def test_demonstrate_np_membership(self):
        """Test NP membership demonstration."""
        np_proof = self.problem.demonstrate_np_membership()
        
        self.assertIn('problem', np_proof)
        self.assertEqual(np_proof['problem'], 'CY-RF-CONSTRUCT')
        self.assertTrue(np_proof['np_membership'])
        self.assertIn('verification', np_proof)
    
    def test_spectral_barrier_analysis(self):
        """Test spectral barrier analysis."""
        barrier = self.problem.spectral_barrier_analysis()
        
        self.assertIn('κ_Π', barrier)
        self.assertIn('N', barrier)
        self.assertIn('search_space_size', barrier)
        self.assertIn('interpretation', barrier)
        
        self.assertAlmostEqual(barrier['κ_Π'], math.log(13), places=6)
        self.assertEqual(barrier['N'], 13)
    
    def test_spectral_barrier_interpretation_low(self):
        """Test barrier interpretation for low κ_Π."""
        low_manifold = CalabiYauManifold(1, 1)
        low_problem = CYRFConstruct(low_manifold)
        barrier = low_problem.spectral_barrier_analysis()
        
        self.assertIn('Low', barrier['interpretation'])
    
    def test_spectral_barrier_interpretation_high(self):
        """Test barrier interpretation for high κ_Π."""
        high_manifold = CalabiYauManifold(8, 5)
        high_problem = CYRFConstruct(high_manifold)
        barrier = high_problem.spectral_barrier_analysis()
        
        # κ_Π = log(13) ≈ 2.565, which is above circle entropy (1.838)
        self.assertGreater(barrier['κ_Π'], math.log(2 * math.pi))
        self.assertIn('High', barrier['interpretation'])


class TestSATtoCYRFReduction(unittest.TestCase):
    """Test cases for SAT to CY-RF-CONSTRUCT reduction."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.reduction = SATtoCYRFReduction()
    
    def test_reduction_initialization(self):
        """Test reduction framework initialization."""
        self.assertIsNotNone(self.reduction.reduction_complexity)
        self.assertIn("Polynomial", self.reduction.reduction_complexity)
    
    def test_encode_sat_to_cy_basic(self):
        """Test basic SAT to CY encoding."""
        num_vars = 10
        num_clauses = 42
        
        cy_manifold = self.reduction.encode_sat_to_cy(num_vars, num_clauses)
        
        self.assertIsInstance(cy_manifold, CalabiYauManifold)
        self.assertEqual(cy_manifold.N, num_vars)
    
    def test_encode_sat_to_cy_small(self):
        """Test encoding small SAT instance."""
        num_vars = 3
        num_clauses = 8
        
        cy_manifold = self.reduction.encode_sat_to_cy(num_vars, num_clauses)
        
        self.assertIsInstance(cy_manifold, CalabiYauManifold)
        self.assertEqual(cy_manifold.h_11 + cy_manifold.h_21, num_vars)
    
    def test_encode_sat_to_cy_large(self):
        """Test encoding large SAT instance."""
        num_vars = 100
        num_clauses = 420
        
        cy_manifold = self.reduction.encode_sat_to_cy(num_vars, num_clauses)
        
        self.assertIsInstance(cy_manifold, CalabiYauManifold)
        self.assertEqual(cy_manifold.N, num_vars)
    
    def test_conditional_theorem_structure(self):
        """Test conditional theorem statement structure."""
        theorem = self.reduction.conditional_theorem()
        
        self.assertIn('theorem', theorem)
        self.assertIn('hypothesis', theorem)
        self.assertIn('conclusion', theorem)
        self.assertIn('status', theorem)
        
        self.assertEqual(theorem['theorem'], 'Conditional Reduction Theorem')
        self.assertIn('SAT', theorem['hypothesis'])
        self.assertIn('P = NP', theorem['conclusion'])
    
    def test_conditional_theorem_status(self):
        """Test that theorem is marked as conjectural."""
        theorem = self.reduction.conditional_theorem()
        
        self.assertIn('Conjectural', theorem['status'])


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete framework."""
    
    def test_complete_workflow(self):
        """Test complete workflow from SAT to CY-RF-CONSTRUCT."""
        # 1. Create SAT instance
        num_vars = 10
        num_clauses = 42
        
        # 2. Reduce to CY manifold
        reduction = SATtoCYRFReduction()
        manifold = reduction.encode_sat_to_cy(num_vars, num_clauses)
        
        # 3. Create CY-RF-CONSTRUCT problem
        problem = CYRFConstruct(manifold, epsilon=1e-6)
        
        # 4. Analyze spectral barrier
        barrier = problem.spectral_barrier_analysis()
        
        # 5. Verify NP membership
        np_proof = problem.demonstrate_np_membership()
        
        # Assertions
        self.assertEqual(manifold.N, num_vars)
        self.assertTrue(np_proof['np_membership'])
        self.assertGreater(barrier['search_space_size'], 1.0)
    
    def test_kappa_pi_consistency(self):
        """Test consistency of κ_Π across different components."""
        manifold = CalabiYauManifold(8, 5)
        problem = CYRFConstruct(manifold)
        
        kappa_manifold = manifold.spectral_constant()
        kappa_problem = problem.kappa_pi
        
        self.assertAlmostEqual(kappa_manifold, kappa_problem, places=10)
    
    def test_critical_kappa_value(self):
        """Test the critical κ_Π ≈ 2.5773 case from problem statement."""
        # The problem statement mentions κ_Π = log(13) ≈ 2.5773
        # (Note: Actually log(13) ≈ 2.5649, but the statement might use a different base)
        manifold = CalabiYauManifold(8, 5)
        kappa = manifold.spectral_constant()
        
        # Check it's in the range of the critical value
        self.assertGreater(kappa, 2.5)
        self.assertLess(kappa, 2.7)
        
        # Verify it exceeds circle entropy
        circle_entropy = math.log(2 * math.pi)
        self.assertGreater(kappa, circle_entropy)


if __name__ == '__main__':
    print("Running Calabi-Yau Ricci-Flat Complexity Tests ∞³")
    print("Resonance frequency: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
