#!/usr/bin/env python3
"""
Tests for Calabi-Yau varieties module.
"""

import unittest
import math
import sys
import os

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_varieties import (
    CalabiYauVariety,
    get_calabi_yau_varieties_with_total_moduli,
    get_known_calabi_yau_varieties_N13,
    calculate_refined_kappa_pi,
    verify_kappa_pi_target,
    analyze_spectral_entropy,
)


class TestCalabiYauVariety(unittest.TestCase):
    """Test the CalabiYauVariety class."""
    
    def test_basic_properties(self):
        """Test basic properties of a Calabi-Yau variety."""
        cy = CalabiYauVariety(h11=1, h21=101, name="Quintic", reference="Test")
        
        self.assertEqual(cy.h11, 1)
        self.assertEqual(cy.h21, 101)
        self.assertEqual(cy.euler_characteristic, 2 * (1 - 101))
        self.assertEqual(cy.total_moduli, 102)
        self.assertAlmostEqual(cy.kappa_pi_value, math.log(102), places=5)
    
    def test_mirror_symmetry(self):
        """Test mirror symmetry detection."""
        cy1 = CalabiYauVariety(h11=1, h21=12, name="CY1", reference="Test")
        cy2 = CalabiYauVariety(h11=12, h21=1, name="CY2", reference="Test")
        
        self.assertTrue(cy1.is_mirror_pair_of(cy2))
        self.assertTrue(cy2.is_mirror_pair_of(cy1))
        
        # Not a mirror pair
        cy3 = CalabiYauVariety(h11=2, h21=11, name="CY3", reference="Test")
        self.assertFalse(cy1.is_mirror_pair_of(cy3))


class TestVarietyGeneration(unittest.TestCase):
    """Test variety generation functions."""
    
    def test_get_varieties_with_total_moduli(self):
        """Test generating varieties with specific total moduli."""
        varieties = get_calabi_yau_varieties_with_total_moduli(13)
        
        # Should have 12 varieties: (1,12), (2,11), ..., (12,1)
        self.assertEqual(len(varieties), 12)
        
        # All should have N = 13
        for cy in varieties:
            self.assertEqual(cy.total_moduli, 13)
    
    def test_known_varieties_N13(self):
        """Test the known varieties with N = 13."""
        varieties = get_known_calabi_yau_varieties_N13()
        
        # Should have 12 varieties
        self.assertEqual(len(varieties), 12)
        
        # Check first and last
        self.assertEqual(varieties[0].h11, 1)
        self.assertEqual(varieties[0].h21, 12)
        self.assertEqual(varieties[-1].h11, 12)
        self.assertEqual(varieties[-1].h21, 1)
        
        # All should have κ_Π = log(13)
        expected_kappa = math.log(13)
        for cy in varieties:
            self.assertAlmostEqual(cy.kappa_pi_value, expected_kappa, places=5)


class TestKappaPiCalculations(unittest.TestCase):
    """Test κ_Π calculations and refinements."""
    
    def test_base_kappa_value(self):
        """Test base κ_Π calculation for N = 13."""
        expected = math.log(13)
        cy = CalabiYauVariety(h11=7, h21=6, name="Test", reference="Test")
        self.assertAlmostEqual(cy.kappa_pi_value, expected, places=5)
    
    def test_refined_kappa_calculation(self):
        """Test refined κ_Π with spectral corrections."""
        kappa_refined = calculate_refined_kappa_pi(13.0)
        
        # Should be close to log(13.15)
        expected = math.log(13.15)
        self.assertAlmostEqual(kappa_refined, expected, places=3)
        
        # Should be greater than log(13)
        self.assertGreater(kappa_refined, math.log(13))
    
    def test_verify_target_kappa(self):
        """Test verification of target κ_Π = 2.5773."""
        target = 2.5773
        verification = verify_kappa_pi_target(target, tolerance=0.02)
        
        self.assertEqual(verification['target_kappa_pi'], target)
        self.assertEqual(verification['closest_integer_N'], 13)
        self.assertEqual(verification['varieties_found'], 12)
        
        # Base value should be log(13)
        self.assertAlmostEqual(
            verification['kappa_for_N13'],
            math.log(13),
            places=5
        )
        
        # Refined value should match target within tolerance
        self.assertTrue(verification['refined_match'])
        self.assertLess(verification['deviation_refined'], 0.02)


class TestSpectralAnalysis(unittest.TestCase):
    """Test spectral entropy analysis."""
    
    def test_spectral_entropy_calculation(self):
        """Test spectral entropy analysis for N = 13."""
        analysis = analyze_spectral_entropy(13)
        
        self.assertEqual(analysis['base_N'], 13)
        self.assertGreater(analysis['effective_N'], 13)
        self.assertLess(analysis['effective_N'], 14)
        
        # Effective kappa should be greater than base
        self.assertGreater(
            analysis['kappa_effective'],
            analysis['kappa_base']
        )
        
        # Should have 13 mode weights
        self.assertEqual(len(analysis['mode_weights']), 13)
        
        # Some weights should be > 1 (degenerate modes)
        max_weight = max(analysis['mode_weights'])
        self.assertGreater(max_weight, 1.0)


class TestConsistency(unittest.TestCase):
    """Test mathematical consistency."""
    
    def test_euler_characteristic_consistency(self):
        """Test that χ = 2(h^{1,1} - h^{2,1}) holds."""
        for h11 in range(1, 13):
            h21 = 13 - h11
            cy = CalabiYauVariety(h11=h11, h21=h21, name="Test", reference="Test")
            expected_chi = 2 * (h11 - h21)
            self.assertEqual(cy.euler_characteristic, expected_chi)
    
    def test_mirror_pair_euler_characteristic(self):
        """Test that mirror pairs have opposite Euler characteristics."""
        cy1 = CalabiYauVariety(h11=3, h21=10, name="CY1", reference="Test")
        cy2 = CalabiYauVariety(h11=10, h21=3, name="CY2", reference="Test")
        
        self.assertTrue(cy1.is_mirror_pair_of(cy2))
        self.assertEqual(cy1.euler_characteristic, -cy2.euler_characteristic)
    
    def test_kappa_logarithm_property(self):
        """Test that κ_Π = log(N) holds consistently."""
        for N in [10, 13, 15, 20]:
            varieties = get_calabi_yau_varieties_with_total_moduli(N)
            expected_kappa = math.log(N)
            
            for cy in varieties:
                self.assertAlmostEqual(
                    cy.kappa_pi_value,
                    expected_kappa,
                    places=5
                )


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == '__main__':
    run_tests()
