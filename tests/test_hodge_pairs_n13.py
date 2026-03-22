#!/usr/bin/env python3
"""
Tests for Hodge Pairs N=13 Analysis

Verifies the calculations for all pairs (h₁,₁, h₂,₁) where h₁,₁ + h₂,₁ = 13
"""

import sys
import os
import math
import unittest

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from analyze_hodge_pairs_n13 import (
    calculate_kappa_pi_for_n,
    PHI,
    KAPPA_PI_SPECTRAL,
    N
)


class TestHodgePairsN13(unittest.TestCase):
    """Test calculations for Hodge pairs with N=13"""
    
    def test_golden_ratio_value(self):
        """Test that φ is calculated correctly."""
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected_phi, places=10)
        self.assertAlmostEqual(PHI, 1.618033988749895, places=10)
    
    def test_golden_ratio_squared(self):
        """Test that φ² = φ + 1 (golden ratio property)."""
        phi_squared = PHI ** 2
        phi_plus_one = PHI + 1
        self.assertAlmostEqual(phi_squared, phi_plus_one, places=10)
    
    def test_kappa_pi_for_n13(self):
        """Test that κ_Π for N=13 is calculated correctly."""
        kappa = calculate_kappa_pi_for_n(13)
        
        # Expected: ln(13) / ln(φ²)
        expected = math.log(13) / math.log(PHI ** 2)
        
        self.assertAlmostEqual(kappa, expected, places=10)
        self.assertAlmostEqual(kappa, 2.665094, places=5)
    
    def test_kappa_pi_is_constant_for_n13(self):
        """Test that κ_Π is constant for all pairs with N=13."""
        # All pairs should give the same κ_Π since N is fixed
        kappa_values = []
        
        for h11 in range(1, 13):
            h21 = 13 - h11
            kappa = calculate_kappa_pi_for_n(h11 + h21)
            kappa_values.append(kappa)
        
        # All values should be the same
        first_kappa = kappa_values[0]
        for kappa in kappa_values:
            self.assertAlmostEqual(kappa, first_kappa, places=10)
    
    def test_difference_with_spectral_constant(self):
        """Test the difference between κ_Π(N=13) and the spectral constant."""
        kappa_n13 = calculate_kappa_pi_for_n(13)
        difference = abs(kappa_n13 - KAPPA_PI_SPECTRAL)
        
        # Should be approximately 0.0878
        self.assertAlmostEqual(difference, 0.0878, places=3)
        
        # Should be less than 0.1
        self.assertLess(difference, 0.1)
    
    def test_ratio_range(self):
        """Test that ratios h₁,₁/h₂,₁ cover the expected range."""
        ratios = []
        
        for h11 in range(1, 13):
            h21 = 13 - h11
            ratio = h11 / h21
            ratios.append(ratio)
        
        # Minimum ratio should be 1/12
        min_ratio = min(ratios)
        self.assertAlmostEqual(min_ratio, 1/12, places=5)
        
        # Maximum ratio should be 12/1
        max_ratio = max(ratios)
        self.assertAlmostEqual(max_ratio, 12.0, places=5)
    
    def test_specific_pairs(self):
        """Test specific pairs mentioned in the problem statement."""
        # h₁,₁ = 9, h₂,₁ = 4 → ratio = 2.25
        ratio_9_4 = 9 / 4
        self.assertAlmostEqual(ratio_9_4, 2.25, places=10)
        
        # h₁,₁ = 10, h₂,₁ = 3 → ratio ≈ 3.33
        ratio_10_3 = 10 / 3
        self.assertAlmostEqual(ratio_10_3, 3.333333, places=5)
    
    def test_closest_to_phi_squared(self):
        """Test which ratio is closest to φ²."""
        phi_squared = PHI ** 2
        
        pairs_and_diffs = []
        for h11 in range(1, 13):
            h21 = 13 - h11
            ratio = h11 / h21
            diff = abs(ratio - phi_squared)
            pairs_and_diffs.append((h11, h21, ratio, diff))
        
        # Find the closest
        closest = min(pairs_and_diffs, key=lambda x: x[3])
        
        # Should be (9, 4) with ratio 2.25
        self.assertEqual(closest[0], 9)
        self.assertEqual(closest[1], 4)
        self.assertAlmostEqual(closest[2], 2.25, places=10)
    
    def test_optimal_n_for_spectral_constant(self):
        """Test that N ≈ 12 gives κ_Π = 2.5773."""
        # Calculate N where κ_Π = KAPPA_PI_SPECTRAL
        # N = φ^(2 * κ_Π)
        optimal_n = PHI ** (2 * KAPPA_PI_SPECTRAL)
        
        # Should be approximately 11.95
        self.assertAlmostEqual(optimal_n, 11.95, places=1)
        
        # Verify that this N gives the spectral constant
        kappa_optimal = calculate_kappa_pi_for_n(optimal_n)
        self.assertAlmostEqual(kappa_optimal, KAPPA_PI_SPECTRAL, places=4)
    
    def test_kappa_formula_consistency(self):
        """Test that the formula κ_Π = ln(N)/ln(φ²) is consistent."""
        test_values = [5, 7, 10, 13, 15, 20]
        
        for n in test_values:
            kappa = calculate_kappa_pi_for_n(n)
            
            # Manual calculation
            expected = math.log(n) / math.log(PHI ** 2)
            
            self.assertAlmostEqual(kappa, expected, places=10)


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties and relationships"""
    
    def test_logarithm_properties(self):
        """Test that ln(φ²) = 2·ln(φ)."""
        ln_phi_squared = math.log(PHI ** 2)
        two_ln_phi = 2 * math.log(PHI)
        
        self.assertAlmostEqual(ln_phi_squared, two_ln_phi, places=10)
    
    def test_kappa_increases_with_n(self):
        """Test that κ_Π increases monotonically with N."""
        n_values = [5, 7, 10, 13, 15, 20, 25, 30]
        kappa_values = [calculate_kappa_pi_for_n(n) for n in n_values]
        
        # Each value should be greater than the previous
        for i in range(1, len(kappa_values)):
            self.assertGreater(kappa_values[i], kappa_values[i-1])


if __name__ == '__main__':
    unittest.main()
