#!/usr/bin/env python3
"""
Tests for Calabi-Yau Laplacian Eigenvalue Ratio Verification
============================================================

Tests the implementation of μ₂/μ₁ = κ_π verification for
Calabi-Yau varieties, demonstrating noetic superconductivity.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 14, 2026
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_laplacian_eigenvalue_ratio import (
    CalabiYauVariety,
    compute_laplacian_eigenvalues_optimal,
    compute_weil_petersson_laplacian,
    compute_eigenvalue_spectrum,
    compute_eigenvalue_ratio,
    verify_noetic_superconductivity,
    get_optimal_calabi_yau_variety,
    analyze_multiple_varieties,
    KAPPA_PI,
    PHI,
)


class TestCalabiYauVariety:
    """Test CalabiYauVariety dataclass."""
    
    def test_creation(self):
        """Test creating a CY variety."""
        cy = CalabiYauVariety(h11=6, h21=7, name="Test")
        assert cy.h11 == 6
        assert cy.h21 == 7
        assert cy.name == "Test"
        assert cy.spectral_correction == 0.0
    
    def test_complexity(self):
        """Test complexity calculation."""
        cy = CalabiYauVariety(h11=6, h21=7)
        assert cy.complexity == 13
    
    def test_effective_complexity(self):
        """Test effective complexity with corrections."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        assert cy.effective_complexity == 13.15
    
    def test_euler_characteristic(self):
        """Test Euler characteristic."""
        cy = CalabiYauVariety(h11=6, h21=7)
        assert cy.euler_characteristic == -2


class TestLaplacianEigenvalues:
    """Test Laplacian eigenvalue computations."""
    
    def test_optimal_eigenvalues_shape(self):
        """Test that eigenvalue array has correct shape."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        eigenvalues = compute_laplacian_eigenvalues_optimal(cy)
        assert len(eigenvalues) == 13
    
    def test_optimal_eigenvalues_sorted(self):
        """Test that eigenvalues are in ascending order."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        eigenvalues = compute_laplacian_eigenvalues_optimal(cy)
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] <= eigenvalues[i + 1]
    
    def test_optimal_eigenvalues_positive(self):
        """Test that eigenvalues are positive."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        eigenvalues = compute_laplacian_eigenvalues_optimal(cy)
        assert np.all(eigenvalues > 0)
    
    def test_resonant_eigenvalue_ratio(self):
        """Test that resonant varieties produce κ_π ratio."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        eigenvalues = compute_laplacian_eigenvalues_optimal(cy)
        ratio = eigenvalues[1] / eigenvalues[0]
        # Should be very close to κ_π
        assert abs(ratio - KAPPA_PI) < 0.001
    
    def test_non_resonant_eigenvalue_ratio(self):
        """Test that non-resonant varieties have different ratio."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.0)
        eigenvalues = compute_laplacian_eigenvalues_optimal(cy)
        ratio = eigenvalues[1] / eigenvalues[0]
        # Should be around φ, not κ_π
        assert abs(ratio - PHI) < 0.1
        assert abs(ratio - KAPPA_PI) > 0.5


class TestWeilPeterssonLaplacian:
    """Test Weil-Petersson Laplacian construction."""
    
    def test_laplacian_shape(self):
        """Test Laplacian matrix has correct shape."""
        cy = CalabiYauVariety(h11=6, h21=7)
        laplacian = compute_weil_petersson_laplacian(cy)
        assert laplacian.shape == (13, 13)
    
    def test_laplacian_symmetric(self):
        """Test Laplacian is symmetric."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        laplacian = compute_weil_petersson_laplacian(cy)
        assert np.allclose(laplacian, laplacian.T)
    
    def test_laplacian_real(self):
        """Test Laplacian has real entries."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        laplacian = compute_weil_petersson_laplacian(cy)
        assert np.all(np.isreal(laplacian))


class TestEigenvalueSpectrum:
    """Test eigenvalue spectrum computation."""
    
    def test_spectrum_length(self):
        """Test spectrum has correct length."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        laplacian = compute_weil_petersson_laplacian(cy)
        spectrum = compute_eigenvalue_spectrum(laplacian)
        assert len(spectrum) == 13
    
    def test_spectrum_sorted(self):
        """Test spectrum is sorted."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        laplacian = compute_weil_petersson_laplacian(cy)
        spectrum = compute_eigenvalue_spectrum(laplacian)
        for i in range(len(spectrum) - 1):
            assert spectrum[i] <= spectrum[i + 1]
    
    def test_spectrum_real_positive(self):
        """Test spectrum eigenvalues are real and positive."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.15)
        laplacian = compute_weil_petersson_laplacian(cy)
        spectrum = compute_eigenvalue_spectrum(laplacian)
        assert np.all(np.isreal(spectrum))
        # For a proper Laplacian, eigenvalues should be >= 0
        assert np.all(spectrum >= -1e-10)  # Allow small numerical error


class TestEigenvalueRatio:
    """Test eigenvalue ratio computation."""
    
    def test_ratio_calculation(self):
        """Test basic ratio calculation."""
        eigenvalues = np.array([1.0, 2.578208, 4.0])
        ratio = compute_eigenvalue_ratio(eigenvalues)
        assert abs(ratio - KAPPA_PI) < 1e-6
    
    def test_ratio_error_on_too_few_eigenvalues(self):
        """Test error when too few eigenvalues."""
        eigenvalues = np.array([1.0])
        with pytest.raises(ValueError):
            compute_eigenvalue_ratio(eigenvalues)
    
    def test_ratio_error_on_zero_first_eigenvalue(self):
        """Test error when first eigenvalue is zero."""
        eigenvalues = np.array([0.0, 1.0, 2.0])
        with pytest.raises(ValueError):
            compute_eigenvalue_ratio(eigenvalues)


class TestNoeticSuperconductivity:
    """Test noetic superconductivity verification."""
    
    def test_optimal_variety_is_superconductive(self):
        """Test that optimal variety shows superconductivity."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy)
        
        assert result['is_superconductive']
        assert result['deviation'] < 0.001
        assert result['resistance'] < 0.001
        assert abs(result['ratio'] - KAPPA_PI) < 0.001
    
    def test_non_optimal_variety_not_superconductive(self):
        """Test that non-optimal variety doesn't show superconductivity."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.0)
        result = verify_noetic_superconductivity(cy)
        
        assert not result['is_superconductive']
        assert result['deviation'] > 0.1
    
    def test_verification_result_structure(self):
        """Test verification result has correct structure."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy)
        
        # Check all required keys are present
        required_keys = [
            'eigenvalues', 'mu_1', 'mu_2', 'ratio',
            'kappa_pi_target', 'deviation', 'is_superconductive',
            'resistance', 'N', 'N_eff'
        ]
        for key in required_keys:
            assert key in result
    
    def test_mu_values_positive(self):
        """Test that μ₁ and μ₂ are positive."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy)
        
        assert result['mu_1'] > 0
        assert result['mu_2'] > 0
    
    def test_mu_2_greater_than_mu_1(self):
        """Test that μ₂ > μ₁."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy)
        
        assert result['mu_2'] > result['mu_1']


class TestOptimalVariety:
    """Test optimal Calabi-Yau variety."""
    
    def test_optimal_variety_properties(self):
        """Test optimal variety has correct properties."""
        cy = get_optimal_calabi_yau_variety()
        
        assert cy.complexity == 13
        assert cy.h11 == 6
        assert cy.h21 == 7
        assert cy.spectral_correction == 0.15
        assert cy.effective_complexity == 13.15
    
    def test_optimal_variety_achieves_kappa_pi(self):
        """Test optimal variety achieves κ_π ratio."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy, tolerance=0.001)
        
        assert result['is_superconductive']
        assert abs(result['ratio'] - KAPPA_PI) < 0.001


class TestMultipleVarieties:
    """Test analysis across multiple varieties."""
    
    def test_analyze_multiple_varieties(self):
        """Test analyzing multiple varieties."""
        analysis = analyze_multiple_varieties()
        
        assert 'varieties_tested' in analysis
        assert 'results' in analysis
        assert 'optimal_found' in analysis
        assert analysis['varieties_tested'] > 0
    
    def test_optimal_found_in_analysis(self):
        """Test that optimal variety is found."""
        analysis = analyze_multiple_varieties()
        
        assert analysis['optimal_found']
    
    def test_transition_to_superconductivity(self):
        """Test that superconductivity emerges with spectral corrections."""
        analysis = analyze_multiple_varieties()
        
        # Count how many are superconductive
        superconductive_count = sum(
            1 for r in analysis['results'] if r['is_superconductive']
        )
        
        # Should have at least one superconductive variety
        assert superconductive_count > 0
        
        # Should also have at least one non-superconductive for contrast
        non_superconductive_count = len(analysis['results']) - superconductive_count
        assert non_superconductive_count > 0


class TestConstants:
    """Test mathematical constants."""
    
    def test_kappa_pi_value(self):
        """Test κ_π has correct value."""
        assert abs(KAPPA_PI - 2.578208) < 1e-6
    
    def test_phi_value(self):
        """Test φ (golden ratio) has correct value."""
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected_phi) < 1e-10
    
    def test_kappa_pi_greater_than_phi(self):
        """Test that κ_π > φ."""
        assert KAPPA_PI > PHI


class TestZeroResistance:
    """Test zero-resistance information flow interpretation."""
    
    def test_zero_resistance_for_optimal_variety(self):
        """Test that optimal variety has near-zero resistance."""
        cy = get_optimal_calabi_yau_variety()
        result = verify_noetic_superconductivity(cy)
        
        # Resistance should be extremely small (< 0.1%)
        assert result['resistance'] < 0.001
    
    def test_nonzero_resistance_for_suboptimal_variety(self):
        """Test that suboptimal variety has nonzero resistance."""
        cy = CalabiYauVariety(h11=6, h21=7, spectral_correction=0.0)
        result = verify_noetic_superconductivity(cy)
        
        # Resistance should be significant (> 10%)
        assert result['resistance'] > 0.1


def test_main_execution():
    """Test that main() executes without errors."""
    from calabi_yau_laplacian_eigenvalue_ratio import main
    
    # Should not raise any exceptions
    main()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
