#!/usr/bin/env python3
"""
Tests for Calabi-Yau κ_Π derivation module.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.calabi_yau_kappa_derivation import (
    PHI,
    PHI_SQUARED,
    kappa_pi_from_hodge_numbers,
    find_N_for_integer_kappa,
    find_N_for_kappa_value,
    verify_kappa_for_N13,
    enumerate_hodge_pairs_for_N,
    find_closest_ratio_to_phi_squared,
    analyze_N13_properties,
)


class TestCalabiYauKappaDerivation(unittest.TestCase):
    """Test cases for Calabi-Yau κ_Π derivation."""
    
    def test_golden_ratio_constants(self):
        """Test that golden ratio constants are correct."""
        # φ = (1 + √5) / 2
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected_phi, places=10)
        
        # φ² = φ + 1
        self.assertAlmostEqual(PHI_SQUARED, PHI + 1, places=10)
        self.assertAlmostEqual(PHI_SQUARED, PHI ** 2, places=10)
        
        # φ² ≈ 2.618033...
        self.assertAlmostEqual(PHI_SQUARED, 2.618033988749895, places=10)
    
    def test_kappa_pi_from_hodge_numbers(self):
        """Test κ_Π calculation from Hodge numbers."""
        # Test N=13: κ_Π = ln(13)/ln(φ²)
        kappa = kappa_pi_from_hodge_numbers(4, 9)  # h^{1,1}=4, h^{2,1}=9
        expected = math.log(13) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(kappa, expected, places=10)
        
        # Test N=12
        kappa_12 = kappa_pi_from_hodge_numbers(6, 6)
        expected_12 = math.log(12) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(kappa_12, expected_12, places=10)
        
    def test_kappa_pi_from_hodge_numbers_errors(self):
        """Test error handling for invalid Hodge numbers."""
        # N must be positive
        with self.assertRaises(ValueError):
            kappa_pi_from_hodge_numbers(0, 0)
        
        with self.assertRaises(ValueError):
            kappa_pi_from_hodge_numbers(-1, 1)
    
    def test_find_N_for_integer_kappa(self):
        """Test finding N for integer κ_Π values."""
        # k=1: N = φ²
        N1 = find_N_for_integer_kappa(1)
        self.assertAlmostEqual(N1, PHI_SQUARED, places=10)
        
        # k=2: N = (φ²)²
        N2 = find_N_for_integer_kappa(2)
        self.assertAlmostEqual(N2, PHI_SQUARED ** 2, places=10)
        
        # k=3: N = (φ²)³
        N3 = find_N_for_integer_kappa(3)
        self.assertAlmostEqual(N3, PHI_SQUARED ** 3, places=10)
    
    def test_find_N_for_kappa_value(self):
        """Test finding N for a given κ_Π value."""
        # κ_Π = 2.5773 should give N ≈ 11.95
        N = find_N_for_kappa_value(2.5773)
        self.assertAlmostEqual(N, 11.95, delta=0.1)
        
        # Verify the reverse calculation
        kappa_back = math.log(N) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(kappa_back, 2.5773, places=4)
    
    def test_verify_kappa_for_N13(self):
        """Test the N=12 and N=13 verification."""
        result = verify_kappa_for_N13()
        
        # Check that all expected keys are present
        self.assertIn('N_12', result)
        self.assertIn('N_13', result)
        self.assertIn('κ_Π_from_N12', result)
        self.assertIn('κ_Π_from_N13', result)
        self.assertIn('κ_Π_established', result)
        self.assertIn('N_from_κ_Π_2.5773', result)
        
        # Verify values
        self.assertEqual(result['N_12'], 12)
        self.assertEqual(result['N_13'], 13)
        self.assertAlmostEqual(result['κ_Π_established'], 2.5773, places=4)
        
        # N=12 should be closer to 2.5773 than N=13
        self.assertLess(result['error_N12'], result['error_N13'])
    
    def test_enumerate_hodge_pairs_for_N(self):
        """Test enumeration of Hodge number pairs."""
        # For N=13, there should be 12 pairs (h^{1,1} from 1 to 12)
        pairs = enumerate_hodge_pairs_for_N(13)
        self.assertEqual(len(pairs), 12)
        
        # All pairs should sum to 13
        for h_11, h_21, ratio in pairs:
            self.assertEqual(h_11 + h_21, 13)
            self.assertAlmostEqual(ratio, h_21 / h_11, places=10)
        
        # First pair: (1, 12)
        self.assertEqual(pairs[0][0], 1)
        self.assertEqual(pairs[0][1], 12)
        self.assertAlmostEqual(pairs[0][2], 12.0, places=10)
        
        # Last pair: (12, 1)
        self.assertEqual(pairs[-1][0], 12)
        self.assertEqual(pairs[-1][1], 1)
        self.assertAlmostEqual(pairs[-1][2], 1/12, places=10)
    
    def test_find_closest_ratio_to_phi_squared(self):
        """Test finding the Hodge pair with ratio closest to φ²."""
        # For N=13, the closest should be (4, 9) with ratio 2.25
        h_11, h_21, ratio, distance = find_closest_ratio_to_phi_squared(13)
        
        self.assertEqual(h_11, 4)
        self.assertEqual(h_21, 9)
        self.assertAlmostEqual(ratio, 2.25, places=10)
        
        # Distance from φ² ≈ 2.618
        expected_distance = abs(2.25 - PHI_SQUARED)
        self.assertAlmostEqual(distance, expected_distance, places=10)
    
    def test_analyze_N13_properties(self):
        """Test complete analysis of N=13 properties."""
        analysis = analyze_N13_properties()
        
        # Check structure
        self.assertIn('N', analysis)
        self.assertIn('κ_Π', analysis)
        self.assertIn('φ²', analysis)
        self.assertIn('hodge_pairs', analysis)
        self.assertIn('closest_to_φ²', analysis)
        self.assertIn('verification', analysis)
        
        # Check values
        self.assertEqual(analysis['N'], 13)
        self.assertAlmostEqual(analysis['φ²'], PHI_SQUARED, places=10)
        
        # Hodge pairs should be 12 pairs
        self.assertEqual(len(analysis['hodge_pairs']), 12)
        
        # Closest to φ² should be (4, 9)
        closest = analysis['closest_to_φ²']
        self.assertEqual(closest['h_11'], 4)
        self.assertEqual(closest['h_21'], 9)
        self.assertAlmostEqual(closest['ratio'], 2.25, places=10)
    
    def test_kappa_pi_consistency_with_constants(self):
        """Test that our derivation is consistent with established constants."""
        from src.constants import KAPPA_PI
        
        # The established κ_Π = 2.5773
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
        
        # This corresponds to N ≈ 11.95
        N_from_kappa = find_N_for_kappa_value(KAPPA_PI)
        self.assertAlmostEqual(N_from_kappa, 11.95, delta=0.1)
        
        # N=12 is the closest integer
        result = verify_kappa_for_N13()
        self.assertEqual(result['closest_integer_N'], 12)


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties of the derivation."""
    
    def test_kappa_pi_is_monotonic(self):
        """Test that κ_Π increases monotonically with N."""
        N_values = [5, 10, 15, 20, 25]
        kappa_values = [
            math.log(N) / math.log(PHI_SQUARED)
            for N in N_values
        ]
        
        # Should be strictly increasing
        for i in range(len(kappa_values) - 1):
            self.assertLess(kappa_values[i], kappa_values[i+1])
    
    def test_logarithmic_scaling(self):
        """Test that κ_Π scales logarithmically with N."""
        # Doubling N should add a constant to κ_Π
        N1 = 10
        N2 = 20
        
        kappa1 = math.log(N1) / math.log(PHI_SQUARED)
        kappa2 = math.log(N2) / math.log(PHI_SQUARED)
        
        delta_kappa = kappa2 - kappa1
        expected_delta = math.log(2) / math.log(PHI_SQUARED)
        
        self.assertAlmostEqual(delta_kappa, expected_delta, places=10)
    
    def test_no_integer_N_gives_integer_kappa(self):
        """Verify that no integer N gives exactly integer κ_Π."""
        # The only N that gives integer κ_Π are N = (φ²)^k, which are all irrational
        # Check integers from 2 to 100
        for N in range(2, 101):
            kappa = math.log(N) / math.log(PHI_SQUARED)
            # κ_Π should never be exactly an integer (but can be close)
            # We check that the fractional part is non-zero
            fractional_part = abs(kappa - round(kappa))
            # Allow very close values (within numerical precision)
            # but ensure it's not exactly an integer
            if fractional_part < 1e-10:
                # This would be essentially an integer, which shouldn't happen
                self.fail(f"N={N} gives κ_Π={kappa} which is too close to integer {round(kappa)}")


if __name__ == '__main__':
    unittest.main()
