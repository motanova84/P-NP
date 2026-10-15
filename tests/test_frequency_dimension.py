#!/usr/bin/env python3
"""
Tests for frequency-dependent complexity framework.

Validates the three-dimensional analysis: Space × Time × Frequency
"""

import unittest
import math
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.constants import (
    KAPPA_PI,
    OMEGA_CRITICAL,
    QCAL_FREQUENCY_HZ,
    spectral_constant_at_frequency,
    information_complexity_at_frequency,
    analyze_three_dimensional_complexity,
    compare_classical_vs_critical_frequency,
)

# Test constants
MIN_EXPECTED_AMPLIFICATION = 10  # Minimum expected complexity amplification at critical frequency


class TestFrequencyDependentComplexity(unittest.TestCase):
    """Test suite for frequency-dependent complexity framework."""
    
    def test_omega_critical_equals_qcal(self):
        """Test that critical frequency equals QCAL frequency."""
        self.assertEqual(OMEGA_CRITICAL, QCAL_FREQUENCY_HZ)
        self.assertEqual(OMEGA_CRITICAL, 141.7001)
    
    def test_spectral_constant_at_zero_frequency(self):
        """Test that at ω=0, κ_Π is constant."""
        for n in [10, 50, 100, 1000]:
            kappa_0 = spectral_constant_at_frequency(0.0, n)
            self.assertAlmostEqual(kappa_0, KAPPA_PI, places=4,
                msg=f"At ω=0, κ_Π should be constant for n={n}")
    
    def test_spectral_constant_decays_at_critical_frequency(self):
        """Test that at ω=ω_c, κ_Π decays with problem size."""
        n_small = 10
        n_large = 100
        
        kappa_small = spectral_constant_at_frequency(OMEGA_CRITICAL, n_small)
        kappa_large = spectral_constant_at_frequency(OMEGA_CRITICAL, n_large)
        
        # At critical frequency, larger problems have smaller κ_Π
        self.assertLess(kappa_large, kappa_small,
            "κ_Π should decay as problem size increases at ω=ω_c")
    
    def test_spectral_constant_decay_rate(self):
        """Test that κ_Π decays as O(1/(√n · log n)) at ω=ω_c."""
        n = 100
        kappa_critical = spectral_constant_at_frequency(OMEGA_CRITICAL, n)
        
        # Expected decay factor: √n · log₂(n)
        expected_decay = math.sqrt(n) * math.log2(n)
        expected_kappa = KAPPA_PI / expected_decay
        
        self.assertAlmostEqual(kappa_critical, expected_kappa, places=4,
            msg="κ_Π should decay as KAPPA_PI / (√n · log n)")
    
    def test_ic_increases_at_critical_frequency(self):
        """Test that IC increases at critical frequency due to κ_Π decay."""
        n = 100
        tw = 50
        
        ic_classical = information_complexity_at_frequency(tw, n, omega=0.0)
        ic_critical = information_complexity_at_frequency(tw, n, omega=OMEGA_CRITICAL)
        
        # At critical frequency, IC should be much larger
        self.assertGreater(ic_critical, ic_classical,
            "IC should increase at critical frequency")
        
        # IC amplification should be significant
        amplification = ic_critical / ic_classical if ic_classical > 0 else float('inf')
        self.assertGreater(amplification, MIN_EXPECTED_AMPLIFICATION,
            f"IC amplification should be at least {MIN_EXPECTED_AMPLIFICATION}x (got {amplification:.2f}x)")
    
    def test_three_dimensional_analysis_classical(self):
        """Test three-dimensional analysis at classical frequency."""
        analysis = analyze_three_dimensional_complexity(
            num_vars=100,
            treewidth=50,
            omega=0.0
        )
        
        # Check that all fields are present
        self.assertIn('space_n', analysis)
        self.assertIn('frequency_omega', analysis)
        self.assertIn('kappa_at_frequency', analysis)
        self.assertIn('time_ic_bits', analysis)
        self.assertIn('spectrum_state', analysis)
        
        # At ω=0, spectrum should be collapsed
        self.assertEqual(analysis['spectrum_state'], 'collapsed')
        self.assertEqual(analysis['frequency_regime'], 'classical (ω=0)')
        self.assertAlmostEqual(analysis['kappa_at_frequency'], KAPPA_PI, places=2)
    
    def test_three_dimensional_analysis_critical(self):
        """Test three-dimensional analysis at critical frequency."""
        analysis = analyze_three_dimensional_complexity(
            num_vars=100,
            treewidth=50,
            omega=OMEGA_CRITICAL
        )
        
        # At ω=ω_c, spectrum should be revealed
        self.assertEqual(analysis['spectrum_state'], 'revealed')
        self.assertIn('critical', analysis['frequency_regime'])
        
        # κ_Π should be much smaller than at classical frequency
        self.assertLess(analysis['kappa_at_frequency'], KAPPA_PI / 10)
    
    def test_comparison_classical_vs_critical(self):
        """Test comparison between classical and critical frequency regimes."""
        comparison = compare_classical_vs_critical_frequency(
            num_vars=100,
            treewidth=50
        )
        
        # Check structure
        self.assertIn('classical_regime', comparison)
        self.assertIn('critical_regime', comparison)
        self.assertIn('comparison', comparison)
        
        # κ_Π should decay at critical frequency
        kappa_ratio = comparison['comparison']['kappa_ratio']
        self.assertGreater(kappa_ratio, MIN_EXPECTED_AMPLIFICATION,
            f"κ_Π should decay significantly (ratio: {kappa_ratio:.2f}x)")
        
        # IC should be amplified at critical frequency
        ic_ratio = comparison['comparison']['IC_ratio']
        self.assertGreater(ic_ratio, MIN_EXPECTED_AMPLIFICATION,
            f"IC should be amplified significantly (ratio: {ic_ratio:.2f}x)")
    
    def test_frequency_interpolation(self):
        """Test that intermediate frequencies interpolate smoothly."""
        n = 100
        
        kappa_0 = spectral_constant_at_frequency(0.0, n)
        kappa_half = spectral_constant_at_frequency(OMEGA_CRITICAL / 2, n)
        kappa_critical = spectral_constant_at_frequency(OMEGA_CRITICAL, n)
        
        # Intermediate frequency should be between classical and critical
        self.assertGreater(kappa_half, kappa_critical,
            "Intermediate frequency should have larger κ_Π than critical")
        self.assertLess(kappa_half, kappa_0,
            "Intermediate frequency should have smaller κ_Π than classical")
    
    def test_edge_cases(self):
        """Test edge cases for frequency-dependent functions."""
        # Small problem sizes
        self.assertGreater(spectral_constant_at_frequency(0.0, 1), 0)
        self.assertGreater(spectral_constant_at_frequency(OMEGA_CRITICAL, 2), 0)
        
        # Large frequencies
        kappa_high = spectral_constant_at_frequency(1000.0, 100)
        self.assertGreater(kappa_high, 0)
        
        # Negative frequencies should work (magnitude matters)
        kappa_neg = spectral_constant_at_frequency(-OMEGA_CRITICAL, 100)
        self.assertGreater(kappa_neg, 0)
    
    def test_consistency_with_classical_bounds(self):
        """Test that classical frequency gives consistent results."""
        n = 100
        tw = 50
        
        # At ω=0, should match classical IC bound formula
        ic_classical = information_complexity_at_frequency(tw, n, 0.0)
        
        # IC should be positive and finite
        self.assertGreater(ic_classical, 0)
        self.assertLess(ic_classical, float('inf'))
        
        # Should scale with treewidth
        ic_double_tw = information_complexity_at_frequency(2 * tw, n, 0.0)
        self.assertAlmostEqual(ic_double_tw, 2 * ic_classical, places=1,
            msg="IC should scale linearly with treewidth at classical frequency")


class TestFrequencyTheory(unittest.TestCase):
    """Test theoretical properties of frequency-dependent complexity."""
    
    def test_spectrum_collapse_at_zero(self):
        """Test that spectrum is collapsed at ω=0."""
        analysis = analyze_three_dimensional_complexity(100, 50, omega=0.0)
        self.assertEqual(analysis['spectrum_state'], 'collapsed')
    
    def test_spectrum_revealed_at_critical(self):
        """Test that spectrum is revealed at ω=ω_c."""
        analysis = analyze_three_dimensional_complexity(100, 50, omega=OMEGA_CRITICAL)
        self.assertEqual(analysis['spectrum_state'], 'revealed')
    
    def test_complexity_amplification_scales_with_size(self):
        """Test that complexity amplification increases with problem size."""
        n_small = 20
        n_large = 100
        tw = 50
        
        # Small problem
        comp_small = compare_classical_vs_critical_frequency(n_small, tw)
        ratio_small = comp_small['comparison']['IC_ratio']
        
        # Large problem
        comp_large = compare_classical_vs_critical_frequency(n_large, tw)
        ratio_large = comp_large['comparison']['IC_ratio']
        
        # Larger problems should have greater amplification
        self.assertGreater(ratio_large, ratio_small,
            "Complexity amplification should increase with problem size")
    
    def test_frequency_independence_for_trivial_problems(self):
        """Test that trivial problems remain tractable at all frequencies."""
        # Very small treewidth should remain tractable
        tw_small = 2
        n = 100
        
        ic_classical = information_complexity_at_frequency(tw_small, n, 0.0)
        ic_critical = information_complexity_at_frequency(tw_small, n, OMEGA_CRITICAL)
        
        # Both should be relatively small
        log_n = math.log2(n)
        self.assertLess(ic_classical, 10 * log_n,
            "Trivial problems should have low IC even at ω=0")
        # Even at critical frequency, small treewidth problems are manageable
        self.assertLess(ic_critical, 100 * log_n,
            "Trivial problems should remain manageable even at ω=ω_c")


if __name__ == '__main__':
    print("=" * 70)
    print("Testing Frequency-Dependent Complexity Framework")
    print("=" * 70)
    print()
    
    # Run tests
    unittest.main(verbosity=2)
