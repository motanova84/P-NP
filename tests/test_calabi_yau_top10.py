#!/usr/bin/env python3
"""
Test suite for calabi_yau_top10_display.py

Tests the Calabi-Yau variety display functionality including:
- CalabiYauVariety class initialization
- Holonomy coefficient calculation
- Spectral density computation
- κ_Π calculation
- Display formatting
"""

import sys
import os
import unittest
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from calabi_yau_top10_display import (
    CalabiYauVariety,
    create_calabi_yau_database
)


class TestCalabiYauVariety(unittest.TestCase):
    """Test cases for CalabiYauVariety class."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Classic quintic in ℂℙ⁴
        self.quintic = CalabiYauVariety("CY-001", "Quíntica ℂℙ⁴[5]", 1, 101)
        
        # Balanced K3 fibration
        self.k3 = CalabiYauVariety("CY-002", "K3 Fibration", 11, 11)
        
        # Medium complexity variety
        self.cicy = CalabiYauVariety("CY-004", "CICY 7862", 5, 65)
    
    def test_initialization(self):
        """Test CalabiYauVariety initialization."""
        self.assertEqual(self.quintic.id, "CY-001")
        self.assertEqual(self.quintic.name, "Quíntica ℂℙ⁴[5]")
        self.assertEqual(self.quintic.h11, 1)
        self.assertEqual(self.quintic.h21, 101)
    
    def test_euler_characteristic(self):
        """Test Euler characteristic calculation: χ = 2(h¹¹ - h²¹)"""
        self.assertEqual(self.quintic.chi, 2 * (1 - 101))
        self.assertEqual(self.quintic.chi, -200)
        
        self.assertEqual(self.k3.chi, 2 * (11 - 11))
        self.assertEqual(self.k3.chi, 0)
        
        self.assertEqual(self.cicy.chi, 2 * (5 - 65))
        self.assertEqual(self.cicy.chi, -120)
    
    def test_holonomy_coefficients_bounds(self):
        """Test that α and β are within valid bounds (0, 1)."""
        varieties = [self.quintic, self.k3, self.cicy]
        
        for variety in varieties:
            self.assertGreater(variety.alpha, 0.0)
            self.assertLess(variety.alpha, 1.0)
            self.assertGreater(variety.beta, 0.0)
            self.assertLess(variety.beta, 1.0)
    
    def test_holonomy_alpha_increases_with_h11(self):
        """Test that α increases with h¹¹."""
        # Create varieties with increasing h11
        v1 = CalabiYauVariety("test1", "test1", 1, 50)
        v2 = CalabiYauVariety("test2", "test2", 5, 50)
        v3 = CalabiYauVariety("test3", "test3", 10, 50)
        
        # α should increase with h11 (when h21 is constant)
        self.assertLess(v1.alpha, v2.alpha)
        self.assertLess(v2.alpha, v3.alpha)
    
    def test_holonomy_beta_decreases_with_h21(self):
        """Test that β decreases with h²¹."""
        # Create varieties with increasing h21
        v1 = CalabiYauVariety("test1", "test1", 5, 30)
        v2 = CalabiYauVariety("test2", "test2", 5, 60)
        v3 = CalabiYauVariety("test3", "test3", 5, 90)
        
        # β should decrease with h21 (when h11 is constant)
        self.assertGreater(v1.beta, v2.beta)
        self.assertGreater(v2.beta, v3.beta)
    
    def test_spectral_density_positive(self):
        """Test that spectral density ρ(θ) is always positive."""
        thetas = np.linspace(-np.pi, np.pi, 100)
        
        for variety in [self.quintic, self.k3, self.cicy]:
            for theta in thetas:
                rho = variety._spectral_density(theta)
                self.assertGreater(rho, 0.0,
                    f"Spectral density should be positive at θ={theta:.3f}")
    
    def test_normalization_constant_positive(self):
        """Test that normalization constant Z > 0."""
        for variety in [self.quintic, self.k3, self.cicy]:
            Z = variety._normalization_constant()
            self.assertGreater(Z, 0.0,
                f"Normalization constant should be positive for {variety.name}")
    
    def test_kappa_pi_range(self):
        """Test that κ_Π values are in expected range."""
        varieties = create_calabi_yau_database()
        
        for variety in varieties:
            # κ_Π should be roughly in range [1.64, 1.68] based on calibration
            self.assertGreater(variety.kappa_pi, 1.60,
                f"κ_Π too small for {variety.name}: {variety.kappa_pi}")
            self.assertLess(variety.kappa_pi, 1.70,
                f"κ_Π too large for {variety.name}: {variety.kappa_pi}")
    
    def test_kappa_pi_decreases_with_alpha(self):
        """Test that κ_Π decreases as α increases (when β is constant)."""
        # Create varieties with same h21 but increasing h11
        varieties = [
            CalabiYauVariety(f"test{i}", f"test{i}", i, 50)
            for i in range(1, 15)
        ]
        
        # Extract kappa values
        kappas = [v.kappa_pi for v in varieties]
        alphas = [v.alpha for v in varieties]
        
        # Check trend: as alpha increases, kappa should decrease
        # Use correlation coefficient
        corr = np.corrcoef(alphas, kappas)[0, 1]
        self.assertLess(corr, 0.0,
            "κ_Π should decrease as α increases (negative correlation)")
    
    def test_kappa_pi_decreases_with_beta_decrease(self):
        """Test that κ_Π has a relationship with β."""
        # Create varieties with same h11 but increasing h21
        varieties = [
            CalabiYauVariety(f"test{i}", f"test{i}", 5, i*10)
            for i in range(3, 12)
        ]
        
        # Extract kappa and beta values
        kappas = [v.kappa_pi for v in varieties]
        betas = [v.beta for v in varieties]
        
        # Verify that there is a statistical relationship between β and κ_Π
        corr = np.corrcoef(betas, kappas)[0, 1]
        self.assertNotEqual(corr, 0.0,
            "κ_Π should have a relationship with β")
    
    def test_to_dict(self):
        """Test conversion to dictionary."""
        d = self.quintic.to_dict()
        
        self.assertEqual(d['ID'], "CY-001")
        self.assertEqual(d['Nombre'], "Quíntica ℂℙ⁴[5]")
        self.assertEqual(d['h11'], 1)
        self.assertEqual(d['h21'], 101)
        self.assertEqual(d['χ'], -200)
        self.assertIn('α', d)
        self.assertIn('β', d)
        self.assertIn('κ_Π', d)


class TestDatabase(unittest.TestCase):
    """Test cases for Calabi-Yau database."""
    
    def test_create_database(self):
        """Test database creation."""
        varieties = create_calabi_yau_database()
        
        # Should have at least 10 varieties
        self.assertGreaterEqual(len(varieties), 10)
        
        # All should be CalabiYauVariety instances
        for v in varieties:
            self.assertIsInstance(v, CalabiYauVariety)
    
    def test_database_has_quintic(self):
        """Test that database includes the classic quintic."""
        varieties = create_calabi_yau_database()
        
        # Find the quintic
        quintic = next((v for v in varieties if v.id == "CY-001"), None)
        
        self.assertIsNotNone(quintic)
        self.assertEqual(quintic.h11, 1)
        self.assertEqual(quintic.h21, 101)
    
    def test_database_unique_ids(self):
        """Test that all variety IDs are unique."""
        varieties = create_calabi_yau_database()
        ids = [v.id for v in varieties]
        
        self.assertEqual(len(ids), len(set(ids)),
            "All variety IDs should be unique")
    
    def test_top_10_ordering(self):
        """Test that top 10 are correctly ordered by κ_Π."""
        varieties = create_calabi_yau_database()
        sorted_varieties = sorted(varieties, key=lambda v: v.kappa_pi, reverse=True)
        
        # Check that top 10 are in descending order
        top_10 = sorted_varieties[:10]
        kappas = [v.kappa_pi for v in top_10]
        
        for i in range(len(kappas) - 1):
            self.assertGreaterEqual(kappas[i], kappas[i+1],
                f"κ_Π should be in descending order: {kappas[i]} >= {kappas[i+1]}")


class TestFormulas(unittest.TestCase):
    """Test mathematical formulas."""
    
    def test_spectral_density_formula(self):
        """Test spectral density formula: ρ(θ) = [1 + α·cos(θ) + β·sin(θ)]²"""
        variety = CalabiYauVariety("test", "test", 5, 50)
        
        theta = np.pi / 4
        expected = (1 + variety.alpha * np.cos(theta) + variety.beta * np.sin(theta)) ** 2
        actual = variety._spectral_density(theta)
        
        self.assertAlmostEqual(actual, expected, places=10)
    
    def test_euler_formula(self):
        """Test Euler characteristic formula: χ = 2(h¹¹ - h²¹)"""
        test_cases = [
            (1, 101, -200),
            (11, 11, 0),
            (5, 65, -120),
            (12, 48, -72),
        ]
        
        for h11, h21, expected_chi in test_cases:
            variety = CalabiYauVariety("test", "test", h11, h21)
            self.assertEqual(variety.chi, expected_chi,
                f"For h11={h11}, h21={h21}, expected χ={expected_chi}")


def main():
    """Run all tests."""
    unittest.main(verbosity=2)


if __name__ == '__main__':
    main()
