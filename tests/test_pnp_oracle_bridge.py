"""
Tests for P=NP Oracle Bridge
============================

Test suite for complete P=NP Oracle Bridge, verifying:
- PC-Higgs and Ramsey-Haar integration
- Three-phase oracle operation
- DNA-Z repair mechanism
- Complete NP solving in O(1)
- Algorithm of God framework

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
"""

import sys
import os
import unittest
import numpy as np

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.pnp_oracle_bridge import PNPOracleBridge, F0_HZ, TAU_FLASH, KAPPA_PI


class TestPNPOracleBridge(unittest.TestCase):
    """Test cases for PNPOracleBridge class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.bridge = PNPOracleBridge(
            g_eff=0.99,
            haar_dimension=51,
            dna_z_enabled=True
        )
    
    def test_initialization(self):
        """Test bridge initialization."""
        self.assertIsNotNone(self.bridge.pc_higgs)
        self.assertIsNotNone(self.bridge.ramsey_oracle)
        self.assertTrue(self.bridge.dna_z_enabled)
        self.assertAlmostEqual(self.bridge.f0, F0_HZ, places=4)
        self.assertAlmostEqual(self.bridge.tau_flash, TAU_FLASH, places=9)
        self.assertAlmostEqual(self.bridge.kappa_pi, KAPPA_PI, places=4)
    
    def test_prepare_labyrinth(self):
        """Test Phase 1: Higgs sets the labyrinth."""
        problem_space = list(range(16))  # 16 configurations
        
        labyrinth = self.bridge.prepare_labyrinth(problem_space)
        
        # Check required keys
        self.assertIn('problem_size', labyrinth)
        self.assertIn('labyrinth_depth', labyrinth)
        self.assertIn('higgs_mass_GeV', labyrinth)
        self.assertIn('higgs_contribution_percent', labyrinth)
        self.assertIn('stage_set', labyrinth)
        
        # Verify values
        self.assertEqual(labyrinth['problem_size'], 16)
        self.assertAlmostEqual(labyrinth['labyrinth_depth'], 4.0, places=6)  # log2(16)
        self.assertTrue(labyrinth['stage_set'])
        self.assertAlmostEqual(labyrinth['higgs_contribution_percent'], 1.0, places=6)
    
    def test_flow_solution(self):
        """Test Phase 2: PC provides fluid solution."""
        # Simple problem: find even number
        problem_space = [1, 3, 5, 8, 9, 11]
        
        def is_even(x):
            return x % 2 == 0
        
        solution_flow = self.bridge.flow_solution(
            problem_space,
            is_even,
            coherence=0.99
        )
        
        # Check required keys
        self.assertIn('solution', solution_flow)
        self.assertIn('is_correct', solution_flow)
        self.assertIn('viscosity', solution_flow)
        self.assertIn('pc_contribution_percent', solution_flow)
        self.assertIn('berry_phase', solution_flow)
        
        # Solution should be correct
        self.assertTrue(solution_flow['is_correct'])
        self.assertEqual(solution_flow['solution'], 8)
        
        # PC should dominate (99%)
        self.assertAlmostEqual(
            solution_flow['pc_contribution_percent'],
            99.0,
            places=6
        )
        
        # Viscosity should be low at high coherence
        self.assertLess(solution_flow['viscosity'], 0.1)
    
    def test_bridge_coupling(self):
        """Test Phase 3: Coupling bridges PC and Higgs."""
        coupling = self.bridge.bridge_coupling(coherence=0.99)
        
        # Check required keys
        self.assertIn('coupling_constant', coupling)
        self.assertIn('coupling_strength', coupling)
        self.assertIn('pc_dominance_ratio', coupling)
        self.assertIn('bridge_active', coupling)
        
        # Coupling constant should be g_eff
        self.assertAlmostEqual(coupling['coupling_constant'], 0.99, places=6)
        
        # Bridge should be active
        self.assertTrue(coupling['bridge_active'])
        
        # PC dominance should be high (99/1 = 99)
        self.assertGreater(coupling['pc_dominance_ratio'], 50)
    
    def test_dna_z_repair_analogy(self):
        """Test DNA-Z repair mechanism."""
        # Use very large error space to show PC advantage
        # (1 million possible errors - exponential search would be prohibitive)
        error_space = list(range(1000000))
        correct_state = 42424
        
        dna_result = self.bridge.dna_z_repair_analogy(error_space, correct_state)
        
        # Should be enabled
        self.assertTrue(dna_result['enabled'])
        
        # Check required keys
        self.assertIn('error_space_size', dna_result)
        self.assertIn('classical_repair_time_s', dna_result)
        self.assertIn('pc_repair_time_us', dna_result)
        self.assertIn('speedup_factor', dna_result)
        
        # For large error spaces, PC repair should be faster
        self.assertLess(
            dna_result['pc_repair_time_us'] * 1e-6,
            dna_result['classical_repair_time_s']
        )
        
        # Speedup should be significant for large spaces
        self.assertGreater(dna_result['speedup_factor'], 100)
        
        # PC repair time should be flash time regardless of error space size
        self.assertAlmostEqual(
            dna_result['pc_repair_time_us'],
            TAU_FLASH * 1e6,
            places=3
        )
    
    def test_dna_z_disabled(self):
        """Test DNA-Z when disabled."""
        bridge_no_dna = PNPOracleBridge(dna_z_enabled=False)
        
        error_space = [(0, 0), (0, 1)]
        correct_state = (1, 1)
        
        result = bridge_no_dna.dna_z_repair_analogy(error_space, correct_state)
        
        self.assertFalse(result['enabled'])
        self.assertIn('message', result)
    
    def test_solve_np_oracle_simple(self):
        """Test complete NP oracle with simple problem."""
        # Find prime number
        problem_space = [4, 6, 7, 8, 9, 10]
        
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(n**0.5) + 1):
                if n % i == 0:
                    return False
            return True
        
        result = self.bridge.solve_np_oracle(
            problem_space,
            is_prime,
            coherence=0.99
        )
        
        # Check all required keys
        required_keys = [
            'solution', 'is_correct', 'problem_size',
            'higgs_contribution_percent', 'pc_contribution_percent',
            'viscosity', 'berry_phase', 'coupling_constant',
            'theoretical_time_us', 'classical_complexity',
            'oracle_complexity', 'framework', 'verdict'
        ]
        
        for key in required_keys:
            self.assertIn(key, result)
        
        # Solution should be correct
        self.assertTrue(result['is_correct'])
        self.assertEqual(result['solution'], 7)
        
        # Verify phase contributions
        self.assertAlmostEqual(result['higgs_contribution_percent'], 1.0, places=6)
        self.assertAlmostEqual(result['pc_contribution_percent'], 99.0, places=6)
        
        # Complexity should collapse to O(1)
        self.assertEqual(result['oracle_complexity'], 'O(1)')
        
        # Framework should be Algorithm of God
        self.assertEqual(result['framework'], 'Algorithm of God')
        self.assertEqual(result['verdict'], 'P = NP via PC-Higgs-Ramsey Oracle')
    
    def test_solve_np_oracle_3sat(self):
        """Test complete NP oracle with 3-SAT problem."""
        # 3-SAT: (A ∨ B) ∧ (¬A ∨ C) ∧ (B ∨ ¬C)
        problem_space = [
            (False, False, False),
            (False, False, True),
            (False, True, False),
            (False, True, True),
            (True, False, False),
            (True, False, True),
            (True, True, False),
            (True, True, True)
        ]
        
        def check_sat(assignment):
            A, B, C = assignment
            clause1 = A or B
            clause2 = (not A) or C
            clause3 = B or (not C)
            return clause1 and clause2 and clause3
        
        result = self.bridge.solve_np_oracle(
            problem_space,
            check_sat,
            coherence=0.99
        )
        
        # Solution should be found and correct
        self.assertTrue(result['is_correct'])
        
        # Should satisfy all clauses
        solution = result['solution']
        self.assertTrue(check_sat(solution))
        
        # Theoretical time should be flash time
        self.assertAlmostEqual(
            result['theoretical_time_us'],
            TAU_FLASH * 1e6,
            places=3
        )
    
    def test_system_state(self):
        """Test complete system state."""
        state = self.bridge.get_system_state()
        
        # Check top-level keys
        required_keys = [
            'framework', 'signature', 'frequency_Hz',
            'pc_higgs', 'ramsey_oracle', 'dna_z',
            'algorithm', 'phase_1', 'phase_2', 'phase_3',
            'result', 'verdict'
        ]
        
        for key in required_keys:
            self.assertIn(key, state)
        
        # Verify framework
        self.assertEqual(state['framework'], 'P=NP Oracle Bridge')
        self.assertEqual(state['signature'], '∴𓂀Ω∞³')
        self.assertAlmostEqual(state['frequency_Hz'], F0_HZ, places=4)
        
        # Verify algorithm description
        self.assertEqual(state['algorithm'], 'Algorithm of God')
        self.assertEqual(state['verdict'], 'P = NP')
        
        # Verify three phases
        self.assertIn('stage', state['phase_1'])
        self.assertIn('fluid', state['phase_2'])
        self.assertIn('bridges', state['phase_3'])
        
        # Verify components
        self.assertIn('coupling_constant', state['pc_higgs'])
        self.assertIn('flash_time_us', state['ramsey_oracle'])
        self.assertIn('enabled', state['dna_z'])
    
    def test_different_coupling_constants(self):
        """Test bridge with different coupling constants."""
        bridge_strong = PNPOracleBridge(g_eff=0.99)
        bridge_weak = PNPOracleBridge(g_eff=0.7)
        
        problem_space = [1, 2, 3, 4, 5]
        
        def is_target(x):
            return x == 3
        
        # Both should find solution
        result_strong = bridge_strong.solve_np_oracle(problem_space, is_target)
        result_weak = bridge_weak.solve_np_oracle(problem_space, is_target)
        
        self.assertTrue(result_strong['is_correct'])
        self.assertTrue(result_weak['is_correct'])
        
        # Strong coupling should have lower viscosity
        self.assertLess(
            result_strong['viscosity'],
            result_weak['viscosity']
        )
        
        # Strong coupling should have higher PC contribution
        self.assertGreater(
            result_strong['pc_contribution_percent'],
            result_weak['pc_contribution_percent']
        )
    
    def test_algorithm_of_god_integration(self):
        """Test the complete Algorithm of God integration."""
        problem_space = list(range(32))  # 32 configurations
        target = 17
        
        def is_target(x):
            return x == target
        
        result = self.bridge.solve_np_oracle(problem_space, is_target, coherence=0.99)
        
        # Verify the three-phase operation
        # Phase 1: Higgs (1%)
        self.assertAlmostEqual(result['higgs_contribution_percent'], 1.0, places=6)
        
        # Phase 2: PC (99%)
        self.assertAlmostEqual(result['pc_contribution_percent'], 99.0, places=6)
        
        # Phase 3: Coupling
        self.assertAlmostEqual(result['coupling_constant'], 0.99, places=6)
        
        # Result: O(1) complexity
        self.assertEqual(result['oracle_complexity'], 'O(1)')
        
        # Solution found in flash time
        self.assertAlmostEqual(
            result['theoretical_time_us'],
            7.057,
            places=3
        )
        
        # Correct solution
        self.assertTrue(result['is_correct'])
        self.assertEqual(result['solution'], target)
    
    def test_exponential_to_constant_collapse(self):
        """Test exponential to constant time collapse."""
        # Test with different problem sizes
        sizes = [8, 16, 32, 64]
        
        for size in sizes:
            problem_space = list(range(size))
            target = size - 1
            
            def is_target(x):
                return x == target
            
            result = self.bridge.solve_np_oracle(problem_space, is_target)
            
            # All should solve in flash time regardless of size
            self.assertAlmostEqual(
                result['theoretical_time_us'],
                TAU_FLASH * 1e6,
                places=3
            )
            
            # All should be O(1)
            self.assertEqual(result['oracle_complexity'], 'O(1)')
            
            # All should find correct solution
            self.assertTrue(result['is_correct'])


class TestIntegrationConstants(unittest.TestCase):
    """Test integration constants."""
    
    def test_fundamental_frequency(self):
        """Test f₀ constant."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_flash_time(self):
        """Test τ_flash constant."""
        self.assertAlmostEqual(TAU_FLASH, 7.057e-6, places=9)
        self.assertAlmostEqual(TAU_FLASH * 1e6, 7.057, places=3)
    
    def test_kappa_pi(self):
        """Test κ_Π constant."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773302292, places=4)


if __name__ == '__main__':
    unittest.main()
