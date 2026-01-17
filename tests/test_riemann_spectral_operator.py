#!/usr/bin/env python3
"""
Tests for Riemann Spectral Operator H_Ψ
=======================================

Tests the implementation of the spectral operator whose eigenvalues
correspond to Riemann zeta zeros, and verifies harmonic alignment with f₀.
"""

import pytest
import numpy as np
from src.riemann_spectral_operator import (
    RiemannSpectralOperator,
    Eigenfunction,
    FrequencyBand,
    F_0,
    T_1,
    DELTA_T,
    RIEMANN_ZEROS,
)


class TestEigenfunction:
    """Tests for the Eigenfunction class."""
    
    def test_eigenfunction_creation(self):
        """Test creating an eigenfunction."""
        ef = Eigenfunction(t=14.134725142, frequency_hz=141.7001, zero_index=0)
        
        assert ef.t == 14.134725142
        assert abs(ef.frequency_hz - 141.7001) < 0.01
        assert ef.zero_index == 0
    
    def test_eigenfunction_evaluation(self):
        """Test evaluating ψ_t(x) at various points."""
        ef = Eigenfunction(t=14.134725142, frequency_hz=141.7001, zero_index=0)
        
        # At x = 1, ψ_t(1) = 1^(-1/2 + it) = 1
        val_1 = ef.evaluate(1.0)
        assert abs(val_1 - 1.0) < 1e-10
        
        # At x > 0, should return complex number
        val_2 = ef.evaluate(2.0)
        assert isinstance(val_2, complex)
        
        # Magnitude should be x^(-1/2)
        x = 2.0
        expected_magnitude = x ** (-0.5)
        actual_magnitude = abs(ef.evaluate(x))
        assert abs(actual_magnitude - expected_magnitude) < 1e-10
    
    def test_eigenfunction_invalid_x(self):
        """Test that negative x raises error."""
        ef = Eigenfunction(t=14.134725142, frequency_hz=141.7001, zero_index=0)
        
        with pytest.raises(ValueError):
            ef.evaluate(-1.0)
        
        with pytest.raises(ValueError):
            ef.evaluate(0.0)
    
    def test_eigenfunction_norm(self):
        """Test that eigenfunctions have finite norm."""
        ef = Eigenfunction(t=14.134725142, frequency_hz=141.7001, zero_index=0)
        
        # Compute ⟨ψ, ψ⟩
        norm_squared = ef.inner_product(ef, x_min=0.1, x_max=10.0)
        
        # Norm should be positive real
        assert norm_squared.imag < 0.1  # Nearly real
        assert norm_squared.real > 0    # Positive
    
    def test_eigenfunction_orthogonality(self):
        """Test approximate orthogonality of different eigenfunctions."""
        ef_0 = Eigenfunction(t=RIEMANN_ZEROS[0], frequency_hz=141.7, zero_index=0)
        ef_1 = Eigenfunction(t=RIEMANN_ZEROS[1], frequency_hz=210.5, zero_index=1)
        
        # Compute ⟨ψ_0, ψ_1⟩
        inner_prod = ef_0.inner_product(ef_1, x_min=0.1, x_max=10.0)
        
        # Should be small (orthogonal)
        assert abs(inner_prod) < 1.0


class TestRiemannSpectralOperator:
    """Tests for the RiemannSpectralOperator class."""
    
    def test_operator_creation(self):
        """Test creating the operator."""
        H_psi = RiemannSpectralOperator()
        
        assert H_psi.f_0 == F_0
        assert len(H_psi.zeros) == len(RIEMANN_ZEROS)
        assert len(H_psi.eigenfunctions) == len(RIEMANN_ZEROS)
    
    def test_operator_custom_zeros(self):
        """Test creating operator with custom zeros."""
        custom_zeros = [10.0, 20.0, 30.0]
        H_psi = RiemannSpectralOperator(zeros=custom_zeros)
        
        assert len(H_psi.zeros) == 3
        assert len(H_psi.eigenfunctions) == 3
    
    def test_get_spectrum(self):
        """Test retrieving the full spectrum."""
        H_psi = RiemannSpectralOperator()
        spectrum = H_psi.get_spectrum()
        
        assert len(spectrum) == len(RIEMANN_ZEROS)
        
        # All eigenvalues should have real part 1/2
        for eigenvalue in spectrum:
            assert abs(eigenvalue.real - 0.5) < 1e-10
        
        # First eigenvalue should match first zero
        assert abs(spectrum[0].imag - RIEMANN_ZEROS[0]) < 1e-10
    
    def test_get_eigenfunction(self):
        """Test retrieving specific eigenfunctions."""
        H_psi = RiemannSpectralOperator()
        
        # Get first eigenfunction
        ef_0 = H_psi.get_eigenfunction(0)
        assert ef_0.zero_index == 0
        assert abs(ef_0.t - RIEMANN_ZEROS[0]) < 1e-10
        
        # Test bounds
        with pytest.raises(IndexError):
            H_psi.get_eigenfunction(-1)
        
        with pytest.raises(IndexError):
            H_psi.get_eigenfunction(len(RIEMANN_ZEROS))
    
    def test_frequency_normalization(self):
        """Test that frequencies are properly normalized."""
        H_psi = RiemannSpectralOperator()
        
        # First zero should normalize to approximately f₀
        t_1 = RIEMANN_ZEROS[0]
        freq_1 = H_psi._normalize_frequency(t_1)
        
        # Should be close to f₀
        assert abs(freq_1 - F_0) < 1.0  # Within 1 Hz
    
    def test_create_frequency_bands(self):
        """Test creating frequency bands."""
        H_psi = RiemannSpectralOperator()
        bands = H_psi.create_frequency_bands(max_bands=10)
        
        assert len(bands) == 10
        
        # Check band properties
        for i, band in enumerate(bands):
            assert band.band_index == i
            assert abs(band.f_min - F_0 * i) < 1e-10
            assert abs(band.f_max - F_0 * (i + 1)) < 1e-10
            
            # Fredholm index should equal number of zeros in band
            assert band.fredholm_index == len(band.zero_frequencies)
            
            # contains_zero should match whether zero_frequencies is non-empty
            assert band.contains_zero == (len(band.zero_frequencies) > 0)
    
    def test_oracle_query(self):
        """Test oracle queries for frequency bands."""
        H_psi = RiemannSpectralOperator()
        
        # Query first few bands
        results = [H_psi.oracle_query(i) for i in range(10)]
        
        # Results should be boolean
        assert all(isinstance(r, bool) for r in results)
        
        # At least some bands should contain zeros (return True)
        assert any(results)
    
    def test_harmonic_alignment(self):
        """Test verification of harmonic alignment with f₀."""
        H_psi = RiemannSpectralOperator()
        alignment = H_psi.verify_harmonic_alignment()
        
        # Check structure of result
        assert 'f_0' in alignment
        assert 'num_zeros' in alignment
        assert 'mean_deviation' in alignment
        assert 'max_deviation' in alignment
        assert 'well_aligned' in alignment
        
        # Values should be reasonable
        assert alignment['f_0'] == F_0
        assert alignment['num_zeros'] == len(RIEMANN_ZEROS)
        assert alignment['mean_deviation'] >= 0
        assert alignment['max_deviation'] >= alignment['mean_deviation']
    
    def test_spacing_statistics(self):
        """Test calculation of zero spacing statistics."""
        H_psi = RiemannSpectralOperator()
        spacing = H_psi.calculate_spacing_statistics()
        
        # Check structure
        assert 'mean_spacing_Δt' in spacing
        assert 'inverse_mean_1/Δt' in spacing
        assert 'std_spacing' in spacing
        assert 'matches_expected' in spacing
        
        # Mean spacing should be positive
        assert spacing['mean_spacing_Δt'] > 0
        
        # Inverse should be reciprocal
        expected_inverse = 1.0 / spacing['mean_spacing_Δt']
        assert abs(spacing['inverse_mean_1/Δt'] - expected_inverse) < 1e-10
        
        # Number of spacings = number of zeros - 1
        assert len(spacing['spacings']) == len(RIEMANN_ZEROS) - 1


class TestFrequencyBand:
    """Tests for the FrequencyBand dataclass."""
    
    def test_frequency_band_creation(self):
        """Test creating a frequency band."""
        band = FrequencyBand(
            band_index=0,
            f_min=0.0,
            f_max=141.7001,
            contains_zero=True,
            zero_frequencies=[141.5],
            fredholm_index=1
        )
        
        assert band.band_index == 0
        assert band.f_min == 0.0
        assert band.f_max == 141.7001
        assert band.contains_zero
        assert len(band.zero_frequencies) == 1
        assert band.fredholm_index == 1
    
    def test_frequency_band_string(self):
        """Test string representation of band."""
        band = FrequencyBand(
            band_index=1,
            f_min=141.7001,
            f_max=283.4002,
            contains_zero=True,
            zero_frequencies=[210.5, 250.3],
            fredholm_index=2
        )
        
        str_repr = str(band)
        
        # Should contain key information
        assert "Band [1]" in str_repr
        assert "141.70" in str_repr
        assert "283.40" in str_repr
        assert "RESONANT" in str_repr
        assert "210.50" in str_repr


class TestIntegration:
    """Integration tests for the full system."""
    
    def test_full_demonstration(self):
        """Test that the full demonstration runs without errors."""
        from src.riemann_spectral_operator import demonstrate_riemann_operator
        
        # Should run without exceptions
        demonstrate_riemann_operator()
    
    def test_spectrum_coverage(self):
        """Test that frequency bands cover the spectrum appropriately."""
        H_psi = RiemannSpectralOperator()
        bands = H_psi.create_frequency_bands(max_bands=30)
        
        # Count total zeros in all bands
        total_zeros_in_bands = sum(len(band.zero_frequencies) for band in bands)
        
        # Should account for most zeros (some may be beyond max_bands)
        assert total_zeros_in_bands >= len(RIEMANN_ZEROS) * 0.8
    
    def test_oracle_consistency(self):
        """Test that oracle results are consistent with band analysis."""
        H_psi = RiemannSpectralOperator()
        bands = H_psi.create_frequency_bands(max_bands=15)
        
        for band in bands:
            oracle_result = H_psi.oracle_query(band.band_index)
            
            # Oracle should match band.contains_zero
            assert oracle_result == band.contains_zero
    
    def test_fredholm_index_nonzero(self):
        """Test that Fredholm index is nonzero when band contains zeros."""
        H_psi = RiemannSpectralOperator()
        bands = H_psi.create_frequency_bands(max_bands=20)
        
        for band in bands:
            if band.contains_zero:
                # Fredholm index should be non-zero
                assert band.fredholm_index != 0
            else:
                # Empty bands have zero index
                assert band.fredholm_index == 0


class TestConstants:
    """Tests for module constants."""
    
    def test_fundamental_frequency(self):
        """Test that f₀ is defined correctly."""
        assert F_0 == 141.7001
    
    def test_first_zero(self):
        """Test that t₁ is the first Riemann zero."""
        assert abs(T_1 - 14.134725142) < 1e-9
    
    def test_delta_t(self):
        """Test expected spacing constant."""
        assert abs(DELTA_T - 28.85) < 0.01
    
    def test_riemann_zeros_ordered(self):
        """Test that Riemann zeros are in ascending order."""
        for i in range(len(RIEMANN_ZEROS) - 1):
            assert RIEMANN_ZEROS[i] < RIEMANN_ZEROS[i + 1]
    
    def test_riemann_zeros_positive(self):
        """Test that all zeros are positive."""
        assert all(z > 0 for z in RIEMANN_ZEROS)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
