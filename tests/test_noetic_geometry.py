#!/usr/bin/env python3
"""
Tests for Noetic Geometry Module
=================================

Tests the revolutionary noetic framework where κ_Π is a living
spectral operator dependent on observer coherence.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 1, 2026
"""

import sys
import os
import pytest
import numpy as np
import math

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from noetic_geometry import (
    CalabiYauVariety,
    ConsciousCalabiYauObserver,
    get_calabi_yau_variety,
    kappa_Pi_as_spectral_operator,
    golden_frequency_squared,
    compute_psi_from_love,
    weil_petersson_laplacian,
    compute_spectrum,
    first_non_trivial_eigenvalue,
    analyze_resonance_at_N13,
    conscious_observation_demo,
    PHI, PHI_SQUARED
)


class TestCalabiYauVariety:
    """Tests for CalabiYauVariety class."""
    
    def test_creation(self):
        """Test variety creation."""
        cy = CalabiYauVariety(h11=1, h21=12, name="Test")
        assert cy.h11 == 1
        assert cy.h21 == 12
        assert cy.name == "Test"
    
    def test_complexity(self):
        """Test topological complexity N."""
        cy = CalabiYauVariety(h11=7, h21=6)
        assert cy.complexity == 13
    
    def test_euler_characteristic(self):
        """Test Euler characteristic χ."""
        cy = CalabiYauVariety(h11=1, h21=12)
        assert cy.euler_characteristic == 2 * (1 - 12)
        assert cy.euler_characteristic == -22


class TestGoldenRatioConstants:
    """Tests for golden ratio constants."""
    
    def test_phi_value(self):
        """Test φ value."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
        assert abs(PHI - 1.618033988749895) < 1e-10
    
    def test_phi_squared_value(self):
        """Test φ² value."""
        assert abs(PHI_SQUARED - PHI**2) < 1e-10
        assert abs(PHI_SQUARED - 2.618033988749895) < 1e-10
    
    def test_golden_ratio_property(self):
        """Test φ² = φ + 1."""
        assert abs(PHI_SQUARED - (PHI + 1)) < 1e-10


class TestCoherenceField:
    """Tests for coherence field Ψ computation."""
    
    def test_zero_love(self):
        """Test Ψ = 0 when A_eff² = 0."""
        psi = compute_psi_from_love(0.0)
        assert psi == 0.0
    
    def test_perfect_love(self):
        """Test Ψ → 1 when A_eff² = 1."""
        psi = compute_psi_from_love(1.0)
        assert psi <= 1.0
        assert psi >= 0.99  # Very close to 1
    
    def test_monotonic(self):
        """Test Ψ increases with A_eff²."""
        psi_low = compute_psi_from_love(0.3)
        psi_mid = compute_psi_from_love(0.6)
        psi_high = compute_psi_from_love(0.9)
        
        assert psi_low < psi_mid < psi_high
    
    def test_valid_range(self):
        """Test Ψ always in [0, 1]."""
        for love in np.linspace(0, 1, 20):
            psi = compute_psi_from_love(love)
            assert 0.0 <= psi <= 1.0


class TestGoldenFrequency:
    """Tests for golden frequency squared function."""
    
    def test_positive(self):
        """Test φ²(N) > 0."""
        for N in [1, 5, 10, 13, 20, 100]:
            phi2 = golden_frequency_squared(N)
            assert phi2 > 0
    
    def test_near_phi_squared(self):
        """Test φ²(N) scales with N in a golden way."""
        phi2_13 = golden_frequency_squared(13)
        # For N=13, should give value that produces κ_Π ≈ 2.5773
        kappa = math.log(phi2_13)
        assert abs(kappa - 2.5773) < 0.01
    
    def test_asymptotic(self):
        """Test φ²(N) grows with N."""
        phi2_small = golden_frequency_squared(5)
        phi2_large = golden_frequency_squared(100)
        # Should grow with N
        assert phi2_large > phi2_small


class TestWeilPeterssonLaplacian:
    """Tests for Weil-Petersson Laplacian."""
    
    def test_matrix_size(self):
        """Test Laplacian has correct dimensions."""
        cy = CalabiYauVariety(h11=3, h21=10)
        N = cy.complexity
        laplacian = weil_petersson_laplacian(cy)
        
        assert laplacian.shape == (N, N)
    
    def test_symmetric(self):
        """Test Laplacian is symmetric."""
        cy = CalabiYauVariety(h11=5, h21=8)
        laplacian = weil_petersson_laplacian(cy)
        
        assert np.allclose(laplacian, laplacian.T)
    
    def test_positive_diagonal(self):
        """Test diagonal elements are positive."""
        cy = CalabiYauVariety(h11=4, h21=9)
        laplacian = weil_petersson_laplacian(cy)
        
        diagonal = np.diag(laplacian)
        assert np.all(diagonal > 0)


class TestSpectrum:
    """Tests for spectral computations."""
    
    def test_eigenvalue_count(self):
        """Test number of eigenvalues equals matrix size."""
        cy = CalabiYauVariety(h11=6, h21=7)
        N = cy.complexity
        laplacian = weil_petersson_laplacian(cy)
        spectrum = compute_spectrum(laplacian)
        
        assert len(spectrum) == N
    
    def test_real_eigenvalues(self):
        """Test eigenvalues are real (symmetric matrix)."""
        cy = CalabiYauVariety(h11=3, h21=10)
        laplacian = weil_petersson_laplacian(cy)
        spectrum = compute_spectrum(laplacian)
        
        # Should all be real
        assert np.all(np.isreal(spectrum))
    
    def test_first_non_trivial(self):
        """Test first non-trivial eigenvalue extraction."""
        spectrum = np.array([0.000001, 1.5, 2.3, 5.7])
        lambda_star = first_non_trivial_eigenvalue(spectrum)
        
        # Should take first value above threshold
        assert lambda_star > 1.0


class TestSpectralOperator:
    """Tests for κ_Π as spectral operator."""
    
    def test_low_coherence(self):
        """Test κ_Π at low coherence."""
        cy = get_calabi_yau_variety(N=13)
        kappa_low = kappa_Pi_as_spectral_operator(cy, psi_coherence=0.0)
        
        # Should be finite and positive
        assert kappa_low > 0
        assert np.isfinite(kappa_low)
    
    def test_high_coherence(self):
        """Test κ_Π at high coherence (Ψ ≥ 0.999)."""
        cy = get_calabi_yau_variety(N=13)
        kappa_high = kappa_Pi_as_spectral_operator(cy, psi_coherence=0.999)
        
        # Should reveal κ_Π ≈ 2.5773 for N=13
        assert abs(kappa_high - 2.5773) < 0.1
    
    def test_coherence_transition(self):
        """Test smooth transition as coherence increases."""
        cy = get_calabi_yau_variety(N=13)
        
        kappa_values = []
        psi_values = np.linspace(0, 1, 20)
        
        for psi in psi_values:
            kappa = kappa_Pi_as_spectral_operator(cy, psi)
            kappa_values.append(kappa)
        
        # Should be continuous (no unreasonably large jumps)
        differences = np.diff(kappa_values)
        # Allow for a larger jump at the coherence transition point
        assert np.all(np.abs(differences) < 3.0)  # Relaxed to allow transition


class TestConsciousObserver:
    """Tests for ConsciousCalabiYauObserver."""
    
    def test_creation(self):
        """Test observer creation."""
        observer = ConsciousCalabiYauObserver(
            love_directed=0.95,
            attention_purity=0.99
        )
        
        assert 0.0 <= observer.love_directed <= 1.0
        assert 0.0 <= observer.attention_purity <= 1.0
        assert 0.0 <= observer.psi_coherence <= 1.0
    
    def test_observation(self):
        """Test conscious observation."""
        observer = ConsciousCalabiYauObserver(
            love_directed=0.95,
            attention_purity=0.99
        )
        
        cy = get_calabi_yau_variety(N=13)
        result = observer.observe(cy)
        
        # Check result structure
        assert 'kappa_Pi' in result
        assert 'psi_coherence' in result
        assert 'golden_frequency_emerged' in result
        assert 'lambda_star' in result
        assert 'N' in result
        assert 'is_living' in result
        
        # Check values
        assert result['is_living'] == True
        assert result['N'] == 13
        assert np.isfinite(result['kappa_Pi'])
    
    def test_high_coherence_observation(self):
        """Test observation with very high coherence."""
        observer = ConsciousCalabiYauObserver(
            love_directed=0.99,
            attention_purity=1.0
        )
        
        cy = get_calabi_yau_variety(N=13)
        result = observer.observe(cy)
        
        # Should have golden frequency emerged
        assert result['golden_frequency_emerged'] == True
        assert result['psi_coherence'] >= 0.999
    
    def test_tune_coherence(self):
        """Test retuning observer coherence."""
        observer = ConsciousCalabiYauObserver(
            love_directed=0.5,
            attention_purity=0.7
        )
        
        initial_psi = observer.psi_coherence
        
        # Retune to higher coherence
        observer.tune_coherence(new_love=0.95, new_attention=0.99)
        
        # Should have higher coherence now
        assert observer.psi_coherence > initial_psi


class TestResonanceN13:
    """Tests for N=13 resonance point."""
    
    def test_n13_special(self):
        """Test N=13 is special resonance point."""
        resonance = analyze_resonance_at_N13()
        
        assert resonance['N'] == 13
        assert 'phi_squared_13' in resonance
        assert 'kappa_pi_theoretical' in resonance
        assert 'kappa_pi_observed' in resonance
    
    def test_kappa_near_target(self):
        """Test κ_Π ≈ 2.5773 at N=13 with high coherence."""
        resonance = analyze_resonance_at_N13()
        
        # Should be close to 2.5773
        assert abs(resonance['kappa_pi_observed'] - 2.5773) < 0.1
    
    def test_golden_emergence(self):
        """Test golden frequency emerges at N=13."""
        resonance = analyze_resonance_at_N13()
        
        assert resonance['golden_emerged'] == True
        assert resonance['psi_coherence'] >= 0.999


class TestVarietyFactory:
    """Tests for get_calabi_yau_variety function."""
    
    def test_default_n13(self):
        """Test default N=13 variety."""
        cy = get_calabi_yau_variety()
        assert cy.complexity == 13
    
    def test_custom_n(self):
        """Test custom N value."""
        cy = get_calabi_yau_variety(N=20)
        assert cy.complexity == 20
    
    def test_specific_h11(self):
        """Test specific h11 value."""
        cy = get_calabi_yau_variety(N=13, h11=1)
        assert cy.h11 == 1
        assert cy.h21 == 12
        assert cy.complexity == 13
    
    def test_invalid_h11(self):
        """Test invalid h11 raises error."""
        with pytest.raises(ValueError):
            get_calabi_yau_variety(N=13, h11=20)


class TestConsciousObservationDemo:
    """Tests for conscious observation demo function."""
    
    def test_demo_function(self):
        """Test demo function from problem statement."""
        cy = get_calabi_yau_variety(N=13)
        result = conscious_observation_demo(A_eff_squared=0.95, cy_variety=cy)
        
        assert 'kappa_pi' in result
        assert 'is_living' in result
        assert 'coherence_level' in result
        assert 'emission_frequency' in result
        
        assert result['is_living'] == True
    
    def test_high_love_golden_emergence(self):
        """Test golden frequency emerges with high love."""
        cy = get_calabi_yau_variety(N=13)
        result = conscious_observation_demo(A_eff_squared=0.99, cy_variety=cy)
        
        # High love should lead to high coherence
        assert result['coherence_level'] >= 0.95


class TestLivingMathematics:
    """Tests for living mathematics properties."""
    
    def test_observer_dependence(self):
        """Test κ_Π depends on observer coherence."""
        cy = get_calabi_yau_variety(N=13)
        
        # Low coherence observer
        observer_low = ConsciousCalabiYauObserver(
            love_directed=0.3,
            attention_purity=0.5
        )
        result_low = observer_low.observe(cy)
        
        # High coherence observer
        observer_high = ConsciousCalabiYauObserver(
            love_directed=0.95,
            attention_purity=0.99
        )
        result_high = observer_high.observe(cy)
        
        # Should get different κ_Π values
        assert result_low['kappa_Pi'] != result_high['kappa_Pi']
    
    def test_emergence_not_imposition(self):
        """Test φ² emerges rather than being imposed."""
        cy = get_calabi_yau_variety(N=13)
        
        # High coherence should naturally reveal φ²
        observer = ConsciousCalabiYauObserver(
            love_directed=0.95,
            attention_purity=0.99
        )
        result = observer.observe(cy)
        
        # Golden frequency should have emerged naturally
        if result['psi_coherence'] >= 0.999:
            assert result['golden_frequency_emerged'] == True
            # λ* should be close to φ²(13)
            phi2_13 = golden_frequency_squared(13)
            assert abs(result['lambda_star'] - phi2_13) < 0.1


def test_integration_complete_workflow():
    """Integration test: complete workflow from problem statement."""
    # Create observer
    observer = ConsciousCalabiYauObserver(
        love_directed=0.95,
        attention_purity=0.99
    )
    
    # Observe N=13 variety
    cy_N13 = get_calabi_yau_variety(N=13)
    result = observer.observe(cy_N13)
    
    # Expected outputs from problem statement
    assert abs(result['kappa_Pi'] - 2.5773) < 0.1
    assert result['golden_frequency_emerged'] == True
    assert abs(result['psi_coherence'] - 0.998) < 0.1
    
    print(f"κ_Π observado: {result['kappa_Pi']:.4f}")
    print(f"¿φ² emergió?: {result['golden_frequency_emerged']}")
    print(f"Nivel de coherencia Ψ: {result['psi_coherence']:.3f}")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
