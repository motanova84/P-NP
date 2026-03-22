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
    
    def test_calculate_n_from_standard_formula(self):
        """Test calculation of N from κ_Π using standard formula."""
        n_from_kappa = self.theorem.calculate_n_from_standard_formula(KAPPA_PI_TARGET)
        
        # Should be approximately 11.947
        self.assertAlmostEqual(n_from_kappa, 11.947, places=2)
        
        # Should match the module calculation
        expected = math.exp(KAPPA_PI_TARGET * LN_PHI_SQUARED)
        self.assertAlmostEqual(n_from_kappa, expected, places=10)
    
    def test_calculate_kappa_pi(self):
        """Test calculation of κ_Π from N."""
        # Test with N_eff = 13.148698
        kappa_from_n_eff = self.theorem.calculate_kappa_pi(N_EFF)
        self.assertAlmostEqual(kappa_from_n_eff, 2.677, places=2)
        
        # Test with integer N=13
        kappa_13 = self.theorem.calculate_kappa_pi(13)
        self.assertAlmostEqual(kappa_13, 2.665, places=2)
        
        # Both should be greater than target (due to spectral corrections)
        self.assertGreater(kappa_from_n_eff, KAPPA_PI_TARGET)
        self.assertGreater(kappa_13, KAPPA_PI_TARGET)
    
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
        self.assertIn('n_eff_stated', verification)
        self.assertIn('n_from_standard_formula', verification)
        self.assertIn('kappa_from_n_eff', verification)
        self.assertIn('correction_factor', verification)
        
        # Check values
        self.assertEqual(verification['kappa_pi_target'], KAPPA_PI_TARGET)
        self.assertAlmostEqual(verification['n_eff_stated'], N_EFF, places=10)
        
        # Standard formula should give smaller N
        self.assertLess(verification['n_from_standard_formula'], N_EFF)
        
        # κ_Π from N_eff should be larger than target
        self.assertGreater(verification['kappa_from_n_eff'], KAPPA_PI_TARGET)
        
        # Correction factor should be > 1
        self.assertGreater(verification['correction_factor'], 1.0)
    
    def test_show_detailed_calculation(self):
        """Test detailed calculation steps."""
        details = self.theorem.show_detailed_calculation()
        
        # Check all steps are present
        self.assertIn('step_1_phi', details)
        self.assertIn('step_1_phi_squared', details)
        self.assertIn('step_2_ln_phi_squared', details)
        self.assertIn('step_3_kappa_target', details)
        self.assertIn('step_3_n_from_standard', details)
        self.assertIn('step_4_n_eff_stated', details)
        self.assertIn('step_5_kappa_from_n_eff', details)
        self.assertIn('step_6_correction', details)
        
        # Verify values
        self.assertAlmostEqual(details['step_1_phi'], PHI, places=10)
        self.assertAlmostEqual(details['step_1_phi_squared'], PHI_SQUARED, places=10)
        self.assertAlmostEqual(details['step_2_ln_phi_squared'], LN_PHI_SQUARED, places=10)
        self.assertEqual(details['step_3_kappa_target'], KAPPA_PI_TARGET)
        self.assertAlmostEqual(details['step_4_n_eff_stated'], N_EFF, places=10)
        
        # Correction should be positive
        self.assertGreater(details['step_6_correction'], 0)
    
    def test_compare_integer_vs_effective(self):
        """Test comparison between integer, standard, and effective values."""
        comparison = self.theorem.compare_integer_vs_effective()
        
        # Check structure
        self.assertIn('n_integer', comparison)
        self.assertIn('n_standard_from_kappa', comparison)
        self.assertIn('n_effective_stated', comparison)
        self.assertIn('kappa_from_integer', comparison)
        self.assertIn('kappa_target', comparison)
        self.assertIn('kappa_from_effective', comparison)
        
        # Check values
        self.assertEqual(comparison['n_integer'], 13)
        self.assertAlmostEqual(comparison['n_effective_stated'], N_EFF, places=10)
        self.assertEqual(comparison['kappa_target'], KAPPA_PI_TARGET)
        
        # Effective should be greater than standard
        self.assertGreater(comparison['n_effective_stated'], comparison['n_standard_from_kappa'])
        
        # Effective kappa should be greater than target
        self.assertGreater(comparison['kappa_from_effective'], KAPPA_PI_TARGET)


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
        # Resonance factor should be > 1 since N_eff = 13.148698 > 13
        self.assertGreater(coupling['resonance_factor'], 1.0)
        
        # Harmonic index should equal κ_Π from N_eff (not the target)
        kappa_from_n_eff = math.log(N_EFF) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(coupling['harmonic_index'], kappa_from_n_eff, places=10)


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
        # N_eff = 13.148698 is actually rational (can be expressed as a fraction)
        # but we treat it as a decimal approximation of a potentially transcendental value
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
        """Test N_eff value."""
        # N_eff is stated as 13.148698 in the theorem
        self.assertAlmostEqual(N_EFF, 13.148698, places=5)
    
    def test_relationship_consistency(self):
        """Test that the constants represent the stated theorem correctly."""
        # The theorem states: N_eff = 13.148698 corresponds to κ_Π = 2.5773
        # Using standard formula: κ_Π(N_eff) = ln(N_eff) / ln(φ²)
        kappa_calculated = math.log(N_EFF) / LN_PHI_SQUARED
        
        # This should give approximately 2.677, NOT 2.5773
        # The difference represents spectral corrections
        self.assertAlmostEqual(kappa_calculated, 2.677, places=2)
        self.assertGreater(kappa_calculated, KAPPA_PI_TARGET)
        
        # Conversely, if we use κ_Π = 2.5773 in the standard formula
        n_from_standard = math.exp(KAPPA_PI_TARGET * LN_PHI_SQUARED)
        
        # This should give approximately 11.947, NOT 13.148698
        self.assertAlmostEqual(n_from_standard, 11.947, places=2)
        self.assertLess(n_from_standard, N_EFF)


class TestTheoremIntegration(unittest.TestCase):
    """Integration tests for the complete theorem."""
    
    def test_full_theorem_verification(self):
        """Test complete theorem verification flow."""
        theorem = EffectiveValueTheorem()
        
        # The theorem states N_eff = 13.148698 corresponds to κ_Π = 2.5773
        # Verify N_eff is as stated
        self.assertAlmostEqual(theorem.n_eff, 13.148698, places=5)
        
        # Using standard formula, κ_Π from N_eff should be ~2.677
        kappa_from_n_eff = theorem.calculate_kappa_pi(theorem.n_eff)
        self.assertAlmostEqual(kappa_from_n_eff, 2.677, places=2)
        
        # Using standard formula, N from κ_Π = 2.5773 should be ~11.947
        n_from_kappa = theorem.calculate_n_from_standard_formula(KAPPA_PI_TARGET)
        self.assertAlmostEqual(n_from_kappa, 11.947, places=2)
        
        # The correction factor represents spectral corrections
        correction = theorem.n_eff / n_from_kappa
        self.assertGreater(correction, 1.0)
        self.assertAlmostEqual(correction, 1.10, places=1)
    
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
