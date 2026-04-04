"""
Tests for Ramsey-Haar Oracle
============================

Test suite for Ramsey-Haar Oracle module, verifying:
- Haar uniform operator generation
- Berry Phase calculation
- Phase wave exploration
- Ramsey order manifestation
- NP problem solving in O(1)

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
"""

import sys
import os
import unittest
import numpy as np

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.ramsey_haar_oracle import (
    RamseyHaarOracle,
    TAU_FLASH,
    RAMSEY_THRESHOLD,
    KAPPA_PI,
    F0_HZ
)


class TestRamseyHaarOracle(unittest.TestCase):
    """Test cases for RamseyHaarOracle class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.oracle = RamseyHaarOracle(haar_dimension=51)
    
    def test_initialization(self):
        """Test oracle initialization."""
        self.assertEqual(self.oracle.haar_dimension, 51)
        self.assertAlmostEqual(self.oracle.tau_flash, TAU_FLASH, places=9)
        self.assertEqual(self.oracle.ramsey_threshold, RAMSEY_THRESHOLD)
        self.assertAlmostEqual(self.oracle.kappa_pi, KAPPA_PI, places=4)
        self.assertAlmostEqual(self.oracle.f0, F0_HZ, places=4)
    
    def test_haar_uniform_operator(self):
        """Test Haar-uniform operator generation."""
        U_haar = self.oracle.haar_uniform_operator(seed=42)
        
        # Check dimensions
        self.assertEqual(U_haar.shape, (51, 51))
        
        # Check unitarity: U†U = I
        U_dagger = np.conjugate(U_haar.T)
        product = U_dagger @ U_haar
        identity = np.eye(51)
        
        # Frobenius norm should be near zero
        error = np.linalg.norm(product - identity, 'fro')
        self.assertLess(error, 1e-10)
        
        # Check determinant magnitude (should be 1)
        det = np.linalg.det(U_haar)
        self.assertAlmostEqual(np.abs(det), 1.0, places=6)
    
    def test_haar_operator_randomness(self):
        """Test that Haar operators are different for different seeds."""
        U1 = self.oracle.haar_uniform_operator(seed=1)
        U2 = self.oracle.haar_uniform_operator(seed=2)
        
        # Operators should be different
        diff = np.linalg.norm(U1 - U2, 'fro')
        self.assertGreater(diff, 0.1)
    
    def test_berry_phase(self):
        """Test Berry Phase calculation."""
        # Simple test with identity Hamiltonian
        n = self.oracle.haar_dimension
        state = np.ones(n, dtype=complex) / np.sqrt(n)
        hamiltonian = np.eye(n, dtype=complex)
        
        gamma = self.oracle.berry_phase(state, hamiltonian)
        
        # Berry phase should be a real number (angle)
        self.assertIsInstance(gamma, (float, np.floating))
        
        # Should be in range [-π, π]
        self.assertGreaterEqual(gamma, -np.pi)
        self.assertLessEqual(gamma, np.pi)
    
    def test_phase_wave_exploration(self):
        """Test phase wave exploration."""
        # Simple problem: find the number 7 in a list
        problem_space = [1, 3, 5, 7, 9, 11, 13]
        
        def fitness(x):
            return 1.0 if x == 7 else 0.0
        
        result = self.oracle.phase_wave_exploration(problem_space, fitness)
        
        # Check result structure
        self.assertIn('solution', result)
        self.assertIn('solution_index', result)
        self.assertIn('berry_phase', result)
        self.assertIn('exploration_time', result)
        self.assertIn('complexity', result)
        
        # Solution should be found
        self.assertEqual(result['solution'], 7)
        
        # Exploration time should be flash time
        self.assertAlmostEqual(result['exploration_time'], TAU_FLASH, places=9)
        
        # Complexity should be O(1)
        self.assertEqual(result['complexity'], 'O(1)')
        
        # Should indicate simultaneous exploration
        self.assertTrue(result['simultaneous_exploration'])
    
    def test_ramsey_order_manifestation(self):
        """Test Ramsey order manifestation."""
        # Below threshold
        result_low = self.oracle.ramsey_order_manifestation(30)
        self.assertFalse(result_low['order_guaranteed'])
        self.assertLess(result_low['coherence'], 1.0)
        
        # At threshold
        result_threshold = self.oracle.ramsey_order_manifestation(51)
        self.assertTrue(result_threshold['order_guaranteed'])
        self.assertAlmostEqual(result_threshold['coherence'], 1.0, places=6)
        
        # Above threshold
        result_high = self.oracle.ramsey_order_manifestation(100)
        self.assertTrue(result_high['order_guaranteed'])
        self.assertAlmostEqual(result_high['coherence'], 1.0, places=6)
        
        # Coherence should increase monotonically
        result_mid = self.oracle.ramsey_order_manifestation(40)
        self.assertGreater(result_mid['coherence'], result_low['coherence'])
        self.assertLess(result_mid['coherence'], result_threshold['coherence'])
    
    def test_solve_np_problem_simple(self):
        """Test NP problem solving with simple example."""
        # Find even number in list
        problem_space = [1, 3, 5, 6, 7, 9]
        
        def is_even(x):
            return x % 2 == 0
        
        result = self.oracle.solve_np_problem(problem_space, is_even)
        
        # Should find the solution
        self.assertTrue(result['is_correct'])
        self.assertEqual(result['solution'], 6)
        
        # Check metrics
        self.assertEqual(result['problem_size'], len(problem_space))
        self.assertEqual(result['complexity'], 'O(1)')
        self.assertIn('ramsey_coherence', result)
        self.assertIn('berry_phase', result)
        self.assertAlmostEqual(
            result['theoretical_time_us'],
            TAU_FLASH * 1e6,
            places=3
        )
    
    def test_solve_np_problem_subset_sum(self):
        """Test NP problem solving with subset sum."""
        # Subset sum: find subset that sums to target
        numbers = [2, 4, 6, 8]
        target = 10
        
        # Generate all subsets
        from itertools import combinations
        problem_space = []
        for r in range(len(numbers) + 1):
            for combo in combinations(numbers, r):
                problem_space.append(list(combo))
        
        def is_correct(subset):
            return sum(subset) == target
        
        result = self.oracle.solve_np_problem(problem_space, is_correct)
        
        # Should find a correct solution
        self.assertTrue(result['is_correct'])
        self.assertEqual(sum(result['solution']), target)
        
        # Verify it's O(1) complexity
        self.assertEqual(result['complexity'], 'O(1)')
    
    def test_haar_unitarity_verification(self):
        """Test Haar unitarity verification."""
        verification = self.oracle.haar_unitarity_verification()
        
        self.assertIn('unitarity_error', verification)
        self.assertIn('determinant_magnitude', verification)
        self.assertIn('is_unitary', verification)
        self.assertIn('verification', verification)
        
        # Should pass verification
        self.assertTrue(verification['is_unitary'])
        self.assertEqual(verification['verification'], 'PASSED')
        
        # Unitarity error should be very small
        self.assertLess(verification['unitarity_error'], 1e-10)
        
        # Determinant magnitude should be 1
        self.assertAlmostEqual(verification['determinant_magnitude'], 1.0, places=6)
    
    def test_oracle_state(self):
        """Test oracle state retrieval."""
        state = self.oracle.get_oracle_state()
        
        # Check required keys
        required_keys = [
            'framework', 'signature', 'frequency_Hz', 'flash_time_us',
            'ramsey_threshold', 'haar_dimension', 'kappa_pi',
            'complexity', 'mechanism', 'convergence'
        ]
        
        for key in required_keys:
            self.assertIn(key, state)
        
        # Verify values
        self.assertEqual(state['signature'], '∴𓂀Ω∞³')
        self.assertAlmostEqual(state['frequency_Hz'], F0_HZ, places=4)
        self.assertAlmostEqual(state['flash_time_us'], TAU_FLASH * 1e6, places=3)
        self.assertEqual(state['ramsey_threshold'], 51)
        self.assertEqual(state['complexity'], 'O(1)')
    
    def test_different_haar_dimensions(self):
        """Test oracle with different Haar dimensions."""
        oracle_small = RamseyHaarOracle(haar_dimension=20)
        oracle_large = RamseyHaarOracle(haar_dimension=100)
        
        # Both should respect minimum Ramsey threshold
        self.assertGreaterEqual(oracle_small.haar_dimension, RAMSEY_THRESHOLD)
        self.assertEqual(oracle_large.haar_dimension, 100)
        
        # Operators should have correct dimensions
        U_small = oracle_small.haar_uniform_operator()
        U_large = oracle_large.haar_uniform_operator()
        
        self.assertEqual(U_small.shape[0], oracle_small.haar_dimension)
        self.assertEqual(U_large.shape[0], oracle_large.haar_dimension)
    
    def test_flash_time_consistency(self):
        """Test that flash time is consistent."""
        self.assertAlmostEqual(self.oracle.tau_flash, 7.057e-6, places=9)
        
        # Flash time in state
        state = self.oracle.get_oracle_state()
        self.assertAlmostEqual(state['flash_time_us'], 7.057, places=3)
    
    def test_kappa_pi_resonance(self):
        """Test κ_Π resonance at Ramsey threshold."""
        result = self.oracle.ramsey_order_manifestation(51)
        
        # At threshold, κ_Π resonance should be maximum
        expected_resonance = result['coherence'] * KAPPA_PI
        self.assertAlmostEqual(
            result['kappa_pi_resonance'],
            expected_resonance,
            places=6
        )
        
        # At threshold, this should be close to κ_Π
        self.assertAlmostEqual(
            result['kappa_pi_resonance'],
            KAPPA_PI,
            places=4
        )


class TestPhysicalConstantsOracle(unittest.TestCase):
    """Test physical constants for oracle."""
    
    def test_flash_time(self):
        """Test flash time constant."""
        self.assertAlmostEqual(TAU_FLASH, 7.057e-6, places=9)
        self.assertAlmostEqual(TAU_FLASH * 1e6, 7.057, places=3)
    
    def test_ramsey_threshold(self):
        """Test Ramsey threshold."""
        self.assertEqual(RAMSEY_THRESHOLD, 51)
    
    def test_kappa_pi(self):
        """Test κ_Π constant."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773302292, places=4)
    
    def test_fundamental_frequency(self):
        """Test f₀."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)


if __name__ == '__main__':
    unittest.main()
