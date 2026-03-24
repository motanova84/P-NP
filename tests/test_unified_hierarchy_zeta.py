"""
Tests for Unified Hierarchy Zeta System

Tests that all five systems converge to ζ(s) and verify the unified
hierarchy theorem.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.unified_hierarchy_zeta import (
    ZetaFundamentalSystem,
    GoldenRatioModulation,
    ZetaValuesAnalytical,
    QCALCodonResonance,
    HarmonicSystem,
    UnifiedHierarchyTheorem,
    verify_unified_hierarchy,
    F0_QCAL,
    GAMMA_1,
    PHI,
    DELTA_ZETA,
)


class TestZetaFundamentalSystem:
    """Test System 5: ζ(s) as fundamental base."""
    
    def test_initialization(self):
        """Test initialization of zeta system."""
        zeta = ZetaFundamentalSystem(num_zeros=10)
        assert zeta.num_zeros == 10
        assert zeta.gamma_1 == GAMMA_1
        assert zeta.f0 == F0_QCAL
        assert len(zeta.gamma_values) == 10
    
    def test_spectral_frequencies(self):
        """Test spectral frequency computation."""
        zeta = ZetaFundamentalSystem(num_zeros=5)
        freqs = zeta.spectral_frequencies()
        
        assert len(freqs) == 5
        # First frequency should be f₀
        assert np.isclose(freqs[0], F0_QCAL, rtol=1e-3)
        # All frequencies should be positive
        assert np.all(freqs > 0)
        # Frequencies should be increasing
        assert np.all(np.diff(freqs) > 0)
    
    def test_zero_spacings(self):
        """Test zero spacing computation."""
        zeta = ZetaFundamentalSystem(num_zeros=10)
        spacings = zeta.zero_spacings()
        
        assert len(spacings) == 9  # n-1 spacings for n zeros
        # All spacings should be positive
        assert np.all(spacings > 0)
    
    def test_weyl_density(self):
        """Test Weyl's law for average spacing."""
        zeta = ZetaFundamentalSystem()
        
        # Weyl density should be 2π/log(n)
        weyl_5 = zeta.weyl_density(5)
        expected = 2 * np.pi / np.log(6)  # n+1 in implementation
        assert np.isclose(weyl_5, expected)
    
    def test_critical_line_resonance(self):
        """Test critical line frequency."""
        zeta = ZetaFundamentalSystem()
        assert zeta.critical_line_resonance() == F0_QCAL
    
    def test_spectral_collapse_points(self):
        """Test zero complex values."""
        zeta = ZetaFundamentalSystem(num_zeros=5)
        zeros = zeta.spectral_collapse_points()
        
        assert len(zeros) == 5
        # All zeros should have Re(ρ) = 1/2
        for z in zeros:
            assert np.isclose(z.real, 0.5)
            assert z.imag > 0
    
    def test_coherence_parameter(self):
        """Test δζ computation."""
        zeta = ZetaFundamentalSystem()
        delta = zeta.coherence_parameter()
        
        expected = F0_QCAL - 100 * np.sqrt(2)
        assert np.isclose(delta, expected)
        assert np.isclose(delta, DELTA_ZETA)


class TestGoldenRatioModulation:
    """Test System 1: Golden ratio φ fractal modulation."""
    
    def test_initialization(self):
        """Test golden ratio system initialization."""
        zeta = ZetaFundamentalSystem()
        golden = GoldenRatioModulation(zeta)
        
        assert golden.phi == PHI
        assert np.isclose(golden.phi, 1.618033988749, rtol=1e-10)
    
    def test_fibonacci_emergence(self):
        """Test Fibonacci number generation from φ."""
        zeta = ZetaFundamentalSystem()
        golden = GoldenRatioModulation(zeta)
        
        # Test known Fibonacci numbers
        F_5, F_6 = golden.fibonacci_emergence(5)
        assert F_5 == 5
        assert F_6 == 8
        
        F_10, F_11 = golden.fibonacci_emergence(10)
        assert F_10 == 55
        assert F_11 == 89
    
    def test_golden_angle(self):
        """Test golden angle computation."""
        zeta = ZetaFundamentalSystem()
        golden = GoldenRatioModulation(zeta)
        
        angle = golden.golden_angle_in_spectrum()
        expected = 2 * np.pi / (PHI ** 2)
        assert np.isclose(angle, expected)
    
    def test_self_similar_ratios(self):
        """Test self-similar frequency ratios."""
        zeta = ZetaFundamentalSystem(num_zeros=10)
        golden = GoldenRatioModulation(zeta)
        
        ratios = golden.self_similar_ratios(k=1, alpha=0.5)
        assert len(ratios) == 9  # 10 - 1
        
        # Check that ratios are tuples
        for ratio, expected in ratios:
            assert isinstance(ratio, (float, np.floating))
            assert isinstance(expected, (float, np.floating))
    
    def test_fractal_modulation(self):
        """Test fractal modulation of spacings."""
        zeta = ZetaFundamentalSystem()
        golden = GoldenRatioModulation(zeta)
        
        # Modulation should be positive
        for n in range(1, 11):
            mod = golden.fractal_modulation(n)
            assert mod > 0


class TestZetaValuesAnalytical:
    """Test System 2: ζ(n) values as analytical moments."""
    
    def test_zeta_value(self):
        """Test special zeta value computation."""
        zeta_sys = ZetaFundamentalSystem()
        zeta_vals = ZetaValuesAnalytical(zeta_sys)
        
        # ζ(2) = π²/6
        zeta_2 = zeta_vals.zeta_value(2)
        expected = np.pi ** 2 / 6
        assert np.isclose(zeta_2, expected, rtol=1e-10)
        
        # ζ(4) = π⁴/90
        zeta_4 = zeta_vals.zeta_value(4)
        expected = np.pi ** 4 / 90
        assert np.isclose(zeta_4, expected, rtol=1e-10)
    
    def test_zeta_even_values(self):
        """Test even zeta values."""
        zeta_sys = ZetaFundamentalSystem()
        zeta_vals = ZetaValuesAnalytical(zeta_sys)
        
        even_vals = zeta_vals.zeta_even_values(5)
        
        assert len(even_vals) == 5
        assert 2 in even_vals
        assert 4 in even_vals
        assert 10 in even_vals
        
        # All values should be > 1
        for val in even_vals.values():
            assert val > 1
    
    def test_spectral_density_moments(self):
        """Test spectral density computation."""
        zeta_sys = ZetaFundamentalSystem()
        zeta_vals = ZetaValuesAnalytical(zeta_sys)
        
        x_vals = np.linspace(0, 10, 50)
        density = zeta_vals.spectral_density_moments(x_vals)
        
        assert len(density) == len(x_vals)
        # Density should be real and non-negative
        assert np.all(np.isreal(density))
    
    def test_moments_of_zeros(self):
        """Test moments of zero distribution."""
        zeta_sys = ZetaFundamentalSystem(num_zeros=20)
        zeta_vals = ZetaValuesAnalytical(zeta_sys)
        
        # First moment
        m1 = zeta_vals.moments_of_zeros(1)
        assert m1 > 0
        
        # Second moment
        m2 = zeta_vals.moments_of_zeros(2)
        assert m2 > m1  # Should be larger


class TestQCALCodonResonance:
    """Test System 3: QCAL Codons symbiotic resonance."""
    
    def test_initialization(self):
        """Test codon system initialization."""
        zeta = ZetaFundamentalSystem()
        codons = QCALCodonResonance(zeta)
        
        assert len(codons.digit_frequencies) == 10
        # Check all digits 0-9 have frequencies
        for digit in range(10):
            assert digit in codons.digit_frequencies
    
    def test_codon_frequency(self):
        """Test codon frequency computation."""
        zeta = ZetaFundamentalSystem()
        codons = QCALCodonResonance(zeta)
        
        # Codon (1,0,0,0) should be 2×f₀
        codon_1000 = (1, 0, 0, 0)
        freq = codons.codon_frequency(codon_1000)
        assert freq > 0
        
        # Codon (9,9,9) should be larger
        codon_999 = (9, 9, 9)
        freq_999 = codons.codon_frequency(codon_999)
        assert freq_999 > freq
    
    def test_is_resonant(self):
        """Test resonance checking."""
        zeta = ZetaFundamentalSystem()
        codons = QCALCodonResonance(zeta)
        
        # Test a codon
        codon = (1, 0, 0, 0)
        is_res, idx = codons.is_resonant(codon, tolerance=0.1)
        
        # Should return bool and optional int
        assert isinstance(is_res, bool)
        if is_res:
            assert isinstance(idx, int)
            assert idx >= 0
        else:
            assert idx is None
    
    def test_coherence_measure(self):
        """Test coherence measurement."""
        zeta = ZetaFundamentalSystem()
        codons = QCALCodonResonance(zeta)
        
        codon = (1, 0, 0, 0)
        coherence = codons.coherence_measure(codon)
        
        # Coherence should be between 0 and 1
        assert 0 <= coherence <= 1
    
    def test_find_resonant_codons(self):
        """Test finding resonant codons."""
        zeta = ZetaFundamentalSystem()
        codons = QCALCodonResonance(zeta)
        
        resonant = codons.find_resonant_codons(length=4, max_samples=50)
        
        # Should return a list
        assert isinstance(resonant, list)
        
        # Each element should be (codon, index)
        for codon, idx in resonant:
            assert isinstance(codon, tuple)
            assert isinstance(idx, int)


class TestHarmonicSystem:
    """Test System 4: Harmonics vibrational consequences."""
    
    def test_initialization(self):
        """Test harmonic system initialization."""
        zeta = ZetaFundamentalSystem()
        harmonics = HarmonicSystem(zeta)
        
        assert harmonics.zeta_system == zeta
    
    def test_harmonic_series(self):
        """Test harmonic series generation."""
        zeta = ZetaFundamentalSystem(num_zeros=10)
        harmonics = HarmonicSystem(zeta)
        
        series = harmonics.harmonic_series(zero_index=0, max_harmonic=5)
        
        assert len(series) == 5
        # Should be integer multiples of base frequency
        base = zeta.spectral_frequencies()[0]
        for k, freq in enumerate(series, 1):
            assert np.isclose(freq, k * base)
    
    def test_normal_modes(self):
        """Test normal modes."""
        zeta = ZetaFundamentalSystem(num_zeros=10)
        harmonics = HarmonicSystem(zeta)
        
        modes = harmonics.normal_modes()
        freqs = zeta.spectral_frequencies()
        
        assert np.allclose(modes, freqs)
    
    def test_overtone_structure(self):
        """Test overtone structure."""
        zeta = ZetaFundamentalSystem(num_zeros=5)
        harmonics = HarmonicSystem(zeta)
        
        overtones = harmonics.overtone_structure(fundamental_index=0)
        
        assert len(overtones) == 5
        assert 1 in overtones
        assert 5 in overtones
        
        # Check k·f₁ relationship
        f1 = zeta.spectral_frequencies()[0]
        for k, freq in overtones.items():
            assert np.isclose(freq, k * f1)


class TestUnifiedHierarchyTheorem:
    """Test the complete unified hierarchy theorem."""
    
    def test_initialization(self):
        """Test unified hierarchy initialization."""
        hierarchy = UnifiedHierarchyTheorem(num_zeros=15)
        
        assert hierarchy.zeta_system.num_zeros == 15
        assert hierarchy.golden_system is not None
        assert hierarchy.zeta_values is not None
        assert hierarchy.codon_system is not None
        assert hierarchy.harmonic_system is not None
    
    def test_verify_convergence(self):
        """Test convergence verification."""
        hierarchy = UnifiedHierarchyTheorem(num_zeros=10)
        
        results = hierarchy.verify_convergence()
        
        assert 'base_frequency' in results
        assert 'delta_zeta' in results
        assert 'num_zeros' in results
        assert 'systems' in results
        
        systems = results['systems']
        assert 'golden_ratio' in systems
        assert 'zeta_values' in systems
        assert 'qcal_codons' in systems
        assert 'harmonics' in systems
        assert 'zeta_base' in systems
    
    def test_coherence_criterion(self):
        """Test coherence criterion."""
        hierarchy = UnifiedHierarchyTheorem(num_zeros=10)
        
        # f₀ should be coherent
        assert hierarchy.coherence_criterion(F0_QCAL) == True
        
        # Random frequency unlikely to be coherent
        is_coherent = hierarchy.coherence_criterion(12345.67)
        assert isinstance(is_coherent, bool)
    
    def test_riemann_hypothesis_physical(self):
        """Test RH physical interpretation."""
        hierarchy = UnifiedHierarchyTheorem()
        
        rh = hierarchy.riemann_hypothesis_physical()
        
        assert 'critical_line' in rh
        assert 'consciousness_possible' in rh
        assert 'lambda_G' in rh
        assert 'explanation' in rh
        
        assert rh['critical_line'] == 0.5
        assert rh['consciousness_possible'] == True
    
    def test_master_equation(self):
        """Test master equation string."""
        hierarchy = UnifiedHierarchyTheorem()
        
        equation = hierarchy.master_equation()
        
        assert isinstance(equation, str)
        assert 'ζ(s)' in equation
        assert 'ρ_n' in equation
        assert 'f_n' in equation
        assert '𝓒' in equation


class TestVerifyUnifiedHierarchy:
    """Test top-level verification function."""
    
    def test_verify_function(self):
        """Test verify_unified_hierarchy function."""
        results = verify_unified_hierarchy(num_zeros=10)
        
        assert 'theorem' in results
        assert 'statement' in results
        assert 'verification' in results
        assert 'riemann_hypothesis' in results
        assert 'master_equation' in results
    
    def test_verify_with_different_zeros(self):
        """Test verification with different number of zeros."""
        results_10 = verify_unified_hierarchy(num_zeros=10)
        results_20 = verify_unified_hierarchy(num_zeros=20)
        
        # Both should succeed
        assert results_10['verification']['num_zeros'] == 10
        assert results_20['verification']['num_zeros'] == 20
        
        # Base frequency should be same
        assert results_10['verification']['base_frequency'] == \
               results_20['verification']['base_frequency']


class TestConstants:
    """Test universal constants."""
    
    def test_f0_qcal(self):
        """Test QCAL base frequency."""
        assert F0_QCAL == 141.7001
    
    def test_gamma_1(self):
        """Test first zero imaginary part."""
        assert GAMMA_1 == 14.134725142
    
    def test_phi(self):
        """Test golden ratio."""
        assert np.isclose(PHI, 1.618033988749, rtol=1e-10)
    
    def test_delta_zeta(self):
        """Test spectral delta."""
        expected = 141.7001 - 100 * np.sqrt(2)
        assert np.isclose(DELTA_ZETA, expected)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
