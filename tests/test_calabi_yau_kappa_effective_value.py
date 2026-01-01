#!/usr/bin/env python3
"""
test_calabi_yau_kappa_effective_value.py - Tests for effective value theorem

Tests the implementation of the theorem showing that κ_Π = 2.5773
emerges from the effective value N_eff = 13.148698.
"""

import unittest
import math
from src.calabi_yau_kappa_effective_value import (
    EffectiveValueTheorem,
    NoeticInterpretation,
    FormalImplications,
    PHI,
    PHI_SQUARED,
    LN_PHI_SQUARED,
    KAPPA_PI_TARGET,
    N_EFF,
)


class TestEffectiveValueTheorem(unittest.TestCase):
    """Test the EffectiveValueTheorem class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.theorem = EffectiveValueTheorem()
    
    def test_initialization(self):
        """Test that the theorem initializes correctly."""
        self.assertAlmostEqual(self.theorem.phi, PHI, places=10)
        self.assertAlmostEqual(self.theorem.phi_squared, PHI_SQUARED, places=10)
        self.assertAlmostEqual(self.theorem.ln_phi_squared, LN_PHI_SQUARED, places=10)
        self.assertEqual(self.theorem.kappa_pi, KAPPA_PI_TARGET)
        self.assertAlmostEqual(self.theorem.n_eff, N_EFF, places=10)
    
    def test_calculate_n_eff(self):
        """Test calculation of N_eff from κ_Π."""
        n_eff = self.theorem.calculate_n_eff(KAPPA_PI_TARGET)
        
        # Should be approximately 13.148698
        self.assertAlmostEqual(n_eff, 13.148698, places=5)
        
        # Should match the module constant
        self.assertAlmostEqual(n_eff, N_EFF, places=10)
    
    def test_calculate_kappa_pi(self):
        """Test calculation of κ_Π from N."""
        # Test with N_eff
        kappa = self.theorem.calculate_kappa_pi(N_EFF)
        self.assertAlmostEqual(kappa, KAPPA_PI_TARGET, places=10)
        
        # Test with integer N=13
        kappa_13 = self.theorem.calculate_kappa_pi(13)
        self.assertAlmostEqual(kappa_13, 2.5649, places=3)
        
        # κ_Π should be less than target for N=13
        self.assertLess(kappa_13, KAPPA_PI_TARGET)
    
    def test_calculate_kappa_pi_invalid_input(self):
        """Test that calculate_kappa_pi raises ValueError for invalid input."""
        with self.assertRaises(ValueError):
            self.theorem.calculate_kappa_pi(0)
        
        with self.assertRaises(ValueError):
            self.theorem.calculate_kappa_pi(-5)
    
    def test_verify_theorem(self):
        """Test theorem verification."""
        verification = self.theorem.verify_theorem()
        
        # Check all expected keys are present
        self.assertIn('kappa_pi_target', verification)
        self.assertIn('n_eff_calculated', verification)
        self.assertIn('kappa_pi_verified', verification)
        self.assertIn('error', verification)
        self.assertIn('verified', verification)
        
        # Check values
        self.assertEqual(verification['kappa_pi_target'], KAPPA_PI_TARGET)
        self.assertAlmostEqual(verification['n_eff_calculated'], N_EFF, places=10)
        self.assertAlmostEqual(verification['kappa_pi_verified'], KAPPA_PI_TARGET, places=10)
        self.assertLess(verification['error'], 1e-10)
        self.assertTrue(verification['verified'])
    
    def test_show_detailed_calculation(self):
        """Test detailed calculation steps."""
        details = self.theorem.show_detailed_calculation()
        
        # Check all steps are present
        self.assertIn('step_1_phi', details)
        self.assertIn('step_1_phi_squared', details)
        self.assertIn('step_2_ln_phi_squared', details)
        self.assertIn('step_3_kappa_times_ln_phi_squared', details)
        self.assertIn('step_4_n_eff', details)
        self.assertIn('step_5_ln_n_eff', details)
        self.assertIn('step_5_verification', details)
        
        # Verify values
        self.assertAlmostEqual(details['step_1_phi'], PHI, places=10)
        self.assertAlmostEqual(details['step_1_phi_squared'], PHI_SQUARED, places=10)
        self.assertAlmostEqual(details['step_2_ln_phi_squared'], LN_PHI_SQUARED, places=10)
        self.assertAlmostEqual(details['step_4_n_eff'], N_EFF, places=10)
        self.assertTrue(details['step_5_verification'])
    
    def test_compare_integer_vs_effective(self):
        """Test comparison between integer and effective values."""
        comparison = self.theorem.compare_integer_vs_effective()
        
        # Check structure
        self.assertIn('n_integer', comparison)
        self.assertIn('n_effective', comparison)
        self.assertIn('n_difference', comparison)
        self.assertIn('kappa_pi_integer', comparison)
        self.assertIn('kappa_pi_effective', comparison)
        self.assertIn('kappa_effective_matches_target', comparison)
        
        # Check values
        self.assertEqual(comparison['n_integer'], 13)
        self.assertAlmostEqual(comparison['n_effective'], N_EFF, places=10)
        self.assertAlmostEqual(comparison['n_difference'], N_EFF - 13, places=10)
        self.assertTrue(comparison['kappa_effective_matches_target'])
        
        # Effective should be greater than integer
        self.assertGreater(comparison['n_effective'], comparison['n_integer'])
        
        # Effective kappa should match target
        self.assertAlmostEqual(comparison['kappa_pi_effective'], KAPPA_PI_TARGET, places=10)


class TestNoeticInterpretation(unittest.TestCase):
    """Test the NoeticInterpretation class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.noetic = NoeticInterpretation()
    
    def test_initialization(self):
        """Test noetic interpretation initialization."""
        self.assertEqual(self.noetic.n_base, 13)
        self.assertAlmostEqual(self.noetic.n_eff, N_EFF, places=10)
        self.assertAlmostEqual(self.noetic.correction, N_EFF - 13, places=10)
    
    def test_decompose_correction(self):
        """Test decomposition of the correction term."""
        contributions = self.noetic.decompose_correction()
        
        # Check required keys
        self.assertIn('total', contributions)
        self.assertIn('spectral_modes', contributions)
        self.assertIn('dual_cycles', contributions)
        self.assertIn('symmetry_corrections', contributions)
        self.assertIn('flux_contributions', contributions)
        
        # Total should equal the correction
        self.assertAlmostEqual(contributions['total'], N_EFF - 13, places=10)
        
        # All contributions should be positive (except possibly residual)
        self.assertGreater(contributions['spectral_modes'], 0)
        self.assertGreater(contributions['dual_cycles'], 0)
        self.assertGreater(contributions['symmetry_corrections'], 0)
        self.assertGreater(contributions['flux_contributions'], 0)
    
    def test_vibrational_interpretation(self):
        """Test vibrational interpretation."""
        vib = self.noetic.vibrational_interpretation()
        
        # Check structure
        self.assertIn('vibrational_degree', vib)
        self.assertIn('fundamental_frequency_scaled', vib)
        self.assertIn('overtones', vib)
        self.assertIn('spectral_density', vib)
        self.assertIn('interpretation', vib)
        
        # Check values
        self.assertAlmostEqual(vib['vibrational_degree'], N_EFF, places=10)
        self.assertEqual(len(vib['overtones']), 5)
        
        # Overtones should be harmonics
        fund_freq = vib['fundamental_frequency_scaled']
        for k, overtone in enumerate(vib['overtones'], 1):
            self.assertAlmostEqual(overtone, fund_freq * k, places=10)
    
    def test_phi_squared_coupling(self):
        """Test φ²-coupling analysis."""
        coupling = self.noetic.phi_squared_coupling()
        
        # Check structure
        self.assertIn('phi_squared', coupling)
        self.assertIn('coupling_strength', coupling)
        self.assertIn('resonance_factor', coupling)
        self.assertIn('harmonic_index', coupling)
        self.assertIn('interpretation', coupling)
        
        # Check values
        self.assertAlmostEqual(coupling['phi_squared'], PHI_SQUARED, places=10)
        self.assertGreater(coupling['resonance_factor'], 1.0)  # Should be > 1 since N_eff > 13
        
        # Harmonic index should equal κ_Π
        self.assertAlmostEqual(coupling['harmonic_index'], KAPPA_PI_TARGET, places=10)


class TestFormalImplications(unittest.TestCase):
    """Test the FormalImplications class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.implications = FormalImplications()
    
    def test_formal_statement(self):
        """Test formal theorem statement generation."""
        statement = self.implications.formal_statement()
        
        # Should be a non-empty string
        self.assertIsInstance(statement, str)
        self.assertGreater(len(statement), 100)
        
        # Should contain key terms
        self.assertIn('TEOREMA', statement)
        self.assertIn('κ_Π', statement)
        self.assertIn('N_eff', statement)
        self.assertIn('DEMOSTRACIÓN', statement)
        self.assertIn('VERIFICACIÓN', statement)
    
    def test_mathematical_properties(self):
        """Test mathematical properties analysis."""
        props = self.implications.mathematical_properties()
        
        # Check structure
        self.assertIn('n_eff', props)
        self.assertIn('is_rational', props)
        self.assertIn('is_irrational', props)
        self.assertIn('is_transcendental', props)
        self.assertIn('nearest_integer', props)
        self.assertIn('distance_to_integer', props)
        
        # Check values
        self.assertAlmostEqual(props['n_eff'], N_EFF, places=10)
        self.assertFalse(props['is_rational'])
        self.assertTrue(props['is_irrational'])
        self.assertTrue(props['is_transcendental'])
        self.assertEqual(props['nearest_integer'], 13)
        self.assertLess(props['distance_to_integer'], 0.5)
    
    def test_reconciliation_with_integer_case(self):
        """Test reconciliation explanation."""
        reconciliation = self.implications.reconciliation_with_integer_case()
        
        # Should be a non-empty string
        self.assertIsInstance(reconciliation, str)
        self.assertGreater(len(reconciliation), 100)
        
        # Should contain key information
        self.assertIn('RECONCILIACIÓN', reconciliation)
        self.assertIn('N = 13', reconciliation)
        self.assertIn('N_eff', reconciliation)
        self.assertIn('Corrección', reconciliation)


class TestConstants(unittest.TestCase):
    """Test module-level constants."""
    
    def test_phi_value(self):
        """Test golden ratio value."""
        expected = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected, places=15)
        self.assertAlmostEqual(PHI, 1.618033988749895, places=10)
    
    def test_phi_squared_value(self):
        """Test φ² value."""
        self.assertAlmostEqual(PHI_SQUARED, PHI ** 2, places=15)
        self.assertAlmostEqual(PHI_SQUARED, 2.618033988749895, places=10)
    
    def test_ln_phi_squared_value(self):
        """Test ln(φ²) value."""
        self.assertAlmostEqual(LN_PHI_SQUARED, math.log(PHI_SQUARED), places=15)
        self.assertAlmostEqual(LN_PHI_SQUARED, 0.96242365, places=7)
    
    def test_kappa_pi_target(self):
        """Test κ_Π target value."""
        self.assertEqual(KAPPA_PI_TARGET, 2.5773)
    
    def test_n_eff_value(self):
        """Test N_eff calculation."""
        expected = math.exp(KAPPA_PI_TARGET * LN_PHI_SQUARED)
        self.assertAlmostEqual(N_EFF, expected, places=15)
        self.assertAlmostEqual(N_EFF, 13.148698, places=5)
    
    def test_relationship_consistency(self):
        """Test that all constants are mathematically consistent."""
        # κ_Π = ln(N_eff) / ln(φ²)
        kappa_calculated = math.log(N_EFF) / LN_PHI_SQUARED
        self.assertAlmostEqual(kappa_calculated, KAPPA_PI_TARGET, places=10)
        
        # N_eff = exp(κ_Π * ln(φ²))
        n_eff_calculated = math.exp(KAPPA_PI_TARGET * LN_PHI_SQUARED)
        self.assertAlmostEqual(n_eff_calculated, N_EFF, places=15)


class TestTheoremIntegration(unittest.TestCase):
    """Integration tests for the complete theorem."""
    
    def test_full_theorem_verification(self):
        """Test complete theorem verification flow."""
        theorem = EffectiveValueTheorem()
        
        # Forward: κ_Π → N_eff
        n_eff = theorem.calculate_n_eff(KAPPA_PI_TARGET)
        self.assertAlmostEqual(n_eff, 13.148698, places=5)
        
        # Reverse: N_eff → κ_Π
        kappa = theorem.calculate_kappa_pi(n_eff)
        self.assertAlmostEqual(kappa, KAPPA_PI_TARGET, places=10)
        
        # Round trip should preserve values
        n_eff_2 = theorem.calculate_n_eff(kappa)
        self.assertAlmostEqual(n_eff_2, n_eff, places=15)
    
    def test_correction_magnitude(self):
        """Test that the correction is in the expected range."""
        noetic = NoeticInterpretation()
        
        # Correction should be positive
        self.assertGreater(noetic.correction, 0)
        
        # Correction should be small (less than 1)
        self.assertLess(noetic.correction, 1)
        
        # Correction should be around 0.148698
        self.assertAlmostEqual(noetic.correction, 0.148698, places=5)
        
        # Correction should be about 1.14% of base value
        correction_percentage = (noetic.correction / 13) * 100
        self.assertAlmostEqual(correction_percentage, 1.14, places=1)
    
    def test_noetic_contributions_sum(self):
        """Test that noetic contributions sum correctly."""
        noetic = NoeticInterpretation()
        contributions = noetic.decompose_correction()
        
        # All individual contributions (excluding total)
        individual_sum = sum(v for k, v in contributions.items() if k != 'total')
        
        # Should equal total
        self.assertAlmostEqual(individual_sum, contributions['total'], places=10)
        
        # Should equal the correction
        self.assertAlmostEqual(contributions['total'], noetic.correction, places=10)


if __name__ == '__main__':
    unittest.main()
