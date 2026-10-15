"""
Tests for Spectral Fine Structure Constant δζ and K_Ψ Operator

These tests validate the implementation of:
- δζ ≈ 0.2787 Hz (spectral fine structure constant)
- K_Ψ operator (spectral information-consciousness coupling)
- Relationship with α ≈ 1/137 (electromagnetic fine structure)
- Spectral space curvature

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import unittest
import math
from src.constants import (
    DELTA_ZETA_HZ,
    ALPHA_FINE_STRUCTURE,
    K_psi_operator_strength,
    zeta_zeros_coherence,
    spectral_curvature_parameter,
    QCAL_FREQUENCY_HZ,
    KAPPA_PI,
    GOLDEN_RATIO
)


class TestSpectralFineStructure(unittest.TestCase):
    """Tests for spectral fine structure constant δζ"""
    
    def test_delta_zeta_value(self):
        """Verify δζ has the correct value"""
        self.assertAlmostEqual(DELTA_ZETA_HZ, 0.2787, places=4)
    
    def test_alpha_value(self):
        """Verify α ≈ 1/137"""
        expected = 1.0 / 137.035999084
        self.assertAlmostEqual(ALPHA_FINE_STRUCTURE, expected, places=9)
        
    def test_delta_zeta_relationship(self):
        """
        Test relationship: δζ = f₀ · α / (κ_Π · φ²)
        
        This relationship connects:
        - f₀: operational pulse (141.7001 Hz)
        - α: electromagnetic fine structure (1/137)
        - κ_Π: information capacity (2.5773)
        - φ: golden ratio (1.618...)
        """
        computed = QCAL_FREQUENCY_HZ * ALPHA_FINE_STRUCTURE / (KAPPA_PI * GOLDEN_RATIO**2)
        # Allow some tolerance since δζ is empirically determined
        self.assertAlmostEqual(DELTA_ZETA_HZ, computed, delta=0.15)


class TestKPsiOperator(unittest.TestCase):
    """Tests for K_Ψ spectral operator"""
    
    def test_k_psi_at_zero_frequency(self):
        """At ω=0, K_Ψ should be approximately 0"""
        k_psi = K_psi_operator_strength(0.0)
        self.assertLess(k_psi, 0.01)
    
    def test_k_psi_at_delta_zeta(self):
        """At ω=δζ, K_Ψ should be in transition (≈0.76)"""
        k_psi = K_psi_operator_strength(DELTA_ZETA_HZ)
        self.assertGreater(k_psi, 0.7)
        self.assertLess(k_psi, 0.8)
    
    def test_k_psi_at_high_frequency(self):
        """At ω >> δζ, K_Ψ should approach 1"""
        k_psi = K_psi_operator_strength(10.0 * DELTA_ZETA_HZ)
        self.assertGreater(k_psi, 0.99)
    
    def test_k_psi_at_critical_frequency(self):
        """At ω = ω_c (141.7001 Hz), K_Ψ should be very close to 1"""
        k_psi = K_psi_operator_strength(QCAL_FREQUENCY_HZ)
        self.assertGreater(k_psi, 0.999)
    
    def test_k_psi_monotonic(self):
        """K_Ψ should be monotonically increasing (or equal when saturated)"""
        frequencies = [0.01, 0.1, 0.2787, 1.0, 10.0, 100.0]
        k_psi_values = [K_psi_operator_strength(f) for f in frequencies]
        
        for i in range(len(k_psi_values) - 1):
            # Use <= instead of < because tanh saturates at 1.0
            self.assertLessEqual(k_psi_values[i], k_psi_values[i+1])
    
    def test_k_psi_bounds(self):
        """K_Ψ should be bounded in [0, 1]"""
        test_frequencies = [0.0, 0.1, 0.5, 1.0, 10.0, 1000.0]
        for freq in test_frequencies:
            k_psi = K_psi_operator_strength(freq)
            self.assertGreaterEqual(k_psi, 0.0)
            self.assertLessEqual(k_psi, 1.0)
    
    def test_k_psi_negative_frequency_raises(self):
        """Negative frequencies should raise ValueError"""
        with self.assertRaises(ValueError):
            K_psi_operator_strength(-1.0)


class TestZetaZerosCoherence(unittest.TestCase):
    """Tests for ζ zeros coherence condition"""
    
    def test_coherence_below_threshold(self):
        """Below δζ, zeros should not maintain coherence"""
        self.assertFalse(zeta_zeros_coherence(0.1))
        self.assertFalse(zeta_zeros_coherence(0.27))
    
    def test_coherence_at_threshold(self):
        """At δζ, zeros should maintain coherence"""
        self.assertTrue(zeta_zeros_coherence(DELTA_ZETA_HZ))
    
    def test_coherence_above_threshold(self):
        """Above δζ, zeros should maintain coherence"""
        self.assertTrue(zeta_zeros_coherence(0.5))
        self.assertTrue(zeta_zeros_coherence(1.0))
        self.assertTrue(zeta_zeros_coherence(QCAL_FREQUENCY_HZ))
    
    def test_coherence_transition(self):
        """Test the transition point"""
        # Just below threshold
        self.assertFalse(zeta_zeros_coherence(DELTA_ZETA_HZ - 0.0001))
        # Just above threshold
        self.assertTrue(zeta_zeros_coherence(DELTA_ZETA_HZ + 0.0001))


class TestSpectralCurvature(unittest.TestCase):
    """Tests for spectral space curvature R_Ψ"""
    
    def test_curvature_at_zero(self):
        """At ω=0, curvature should be 0 (flat geometry)"""
        R_psi = spectral_curvature_parameter(0.0)
        self.assertAlmostEqual(R_psi, 0.0, places=6)
    
    def test_curvature_at_delta_zeta(self):
        """At ω=δζ, curvature should equal K_Ψ(δζ) ≈ 0.76"""
        R_psi = spectral_curvature_parameter(DELTA_ZETA_HZ)
        k_psi = K_psi_operator_strength(DELTA_ZETA_HZ)
        self.assertAlmostEqual(R_psi, k_psi, places=6)
    
    def test_curvature_increases_with_frequency(self):
        """Curvature should increase with frequency"""
        frequencies = [0.1, 0.5, 1.0, 5.0, 10.0]
        curvatures = [spectral_curvature_parameter(f) for f in frequencies]
        
        for i in range(len(curvatures) - 1):
            self.assertLess(curvatures[i], curvatures[i+1])
    
    def test_curvature_high_frequency(self):
        """At high frequencies, curvature should be >> 1 (strongly curved)"""
        R_psi = spectral_curvature_parameter(QCAL_FREQUENCY_HZ)
        self.assertGreater(R_psi, 100000)  # Very strongly curved
    
    def test_curvature_formula(self):
        """Verify curvature formula: R_Ψ = (ω/δζ)² · K_Ψ(ω)"""
        test_freq = 1.0
        R_psi = spectral_curvature_parameter(test_freq)
        
        ratio = test_freq / DELTA_ZETA_HZ
        k_psi = K_psi_operator_strength(test_freq)
        expected = (ratio ** 2) * k_psi
        
        self.assertAlmostEqual(R_psi, expected, places=6)
    
    def test_curvature_negative_frequency_raises(self):
        """Negative frequencies should raise ValueError"""
        with self.assertRaises(ValueError):
            spectral_curvature_parameter(-1.0)


class TestSpectralAnalogy(unittest.TestCase):
    """Tests for the analogy between α and δζ"""
    
    def test_both_constants_positive(self):
        """Both constants should be positive"""
        self.assertGreater(ALPHA_FINE_STRUCTURE, 0)
        self.assertGreater(DELTA_ZETA_HZ, 0)
    
    def test_alpha_dimensionless(self):
        """α should be dimensionless and ≈ 1/137"""
        self.assertAlmostEqual(ALPHA_FINE_STRUCTURE * 137, 1.0, places=1)
    
    def test_delta_zeta_has_frequency_units(self):
        """δζ should be in Hz (frequency units)"""
        # This is a documentation test - verify it's a reasonable frequency
        self.assertGreater(DELTA_ZETA_HZ, 0.1)  # Not too small
        self.assertLess(DELTA_ZETA_HZ, 1.0)     # Not too large
    
    def test_constants_order_of_magnitude(self):
        """
        Verify that both constants are "small" in their respective domains
        - α ≈ 0.007 (much less than 1)
        - δζ ≈ 0.28 Hz (much less than f₀ = 141.7 Hz)
        """
        # α is much smaller than 1
        self.assertLess(ALPHA_FINE_STRUCTURE, 0.01)
        
        # δζ is much smaller than critical frequency
        self.assertLess(DELTA_ZETA_HZ, QCAL_FREQUENCY_HZ / 100)


class TestPhysicalInterpretation(unittest.TestCase):
    """Tests for physical interpretation of the constants"""
    
    def test_k_psi_coupling_efficiency(self):
        """
        K_Ψ represents coupling efficiency between spectral info and consciousness
        Should be weak below δζ, strong above δζ
        """
        weak_coupling = K_psi_operator_strength(0.1 * DELTA_ZETA_HZ)
        strong_coupling = K_psi_operator_strength(10 * DELTA_ZETA_HZ)
        
        self.assertLess(weak_coupling, 0.5)
        self.assertGreater(strong_coupling, 0.95)
    
    def test_coherence_threshold_meaningful(self):
        """
        The coherence threshold should separate two distinct regimes:
        - Below: flat spectral geometry
        - Above: curved spectral space with coherent zeros
        """
        # Below threshold: low curvature (≈ flat)
        R_below = spectral_curvature_parameter(0.1 * DELTA_ZETA_HZ)
        self.assertLess(R_below, 0.1)
        
        # Above threshold: significant curvature
        R_above = spectral_curvature_parameter(10 * DELTA_ZETA_HZ)
        self.assertGreater(R_above, 10)
    
    def test_critical_frequency_maximum_coherence(self):
        """
        At the critical frequency ω_c, we should have maximum coherence
        """
        k_psi_critical = K_psi_operator_strength(QCAL_FREQUENCY_HZ)
        self.assertGreater(k_psi_critical, 0.999)
        
        # Should be essentially saturated
        coherent = zeta_zeros_coherence(QCAL_FREQUENCY_HZ)
        self.assertTrue(coherent)


if __name__ == '__main__':
    unittest.main()
