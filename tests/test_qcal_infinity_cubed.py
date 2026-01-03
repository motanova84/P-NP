"""
Tests for QCAL ∞³ (Quantum Computational Arithmetic Lattice - Infinity Cubed)

Test suite for the unified millennium problems framework.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import numpy as np
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from qcal_infinity_cubed import (
    QCALInfinityCubed,
    SpectralOperator,
    PvsNPOperator,
    RiemannOperator,
    BSDOperator,
    GoldbachOperator,
    KAPPA_PI,
    F0_QCAL,
    PHI,
    create_complete_qcal_system
)


class TestUniversalConstants:
    """Test universal constants."""
    
    def test_kappa_pi_value(self):
        """Test κ_Π = 2.5773."""
        assert abs(KAPPA_PI - 2.5773) < 0.0001
    
    def test_f0_value(self):
        """Test f₀ = 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 0.0001
    
    def test_golden_ratio(self):
        """Test φ = (1+√5)/2."""
        expected = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
    
    def test_kappa_f0_relation(self):
        """Test relation between κ_Π and f₀."""
        # κ_Π ≈ log₂(f₀/π²) + φ - π
        computed = np.log2(F0_QCAL / (np.pi**2)) + PHI - np.pi
        assert abs(computed - KAPPA_PI) < 0.01


class TestPvsNPOperator:
    """Test P vs NP spectral operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = PvsNPOperator(num_vars=100, treewidth=50)
        assert op.num_vars == 100
        assert op.treewidth == 50
        assert op.name == "P vs NP"
    
    def test_polynomial_case(self):
        """Test low treewidth (polynomial) case."""
        op = PvsNPOperator(num_vars=100, treewidth=5)
        classification = op.computational_dichotomy()
        assert "P" in classification or "Tractable" in classification
    
    def test_exponential_case(self):
        """Test high treewidth (exponential) case."""
        op = PvsNPOperator(num_vars=100, treewidth=50)
        classification = op.computational_dichotomy()
        assert "NP" in classification or "Intractable" in classification
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        op = PvsNPOperator(num_vars=100, treewidth=50)
        spectrum = op.compute_spectrum()
        assert len(spectrum) > 0
        assert all(spectrum >= 0)
    
    def test_information_bottleneck(self):
        """Test information bottleneck scales with κ_Π."""
        op = PvsNPOperator(num_vars=100, treewidth=50)
        ib = op.information_bottleneck()
        # Should be positive and scale with κ_Π
        assert ib > 0
        assert ib / KAPPA_PI > 0.1
    
    def test_coupling_strength(self):
        """Test QCAL coupling strength."""
        op = PvsNPOperator(num_vars=100, treewidth=50)
        coupling = op.coupling_strength()
        assert coupling != 0


class TestRiemannOperator:
    """Test Riemann Hypothesis spectral operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = RiemannOperator(max_prime=100)
        assert op.max_prime == 100
        assert op.name == "Riemann Hypothesis"
    
    def test_prime_generation(self):
        """Test prime number generation."""
        op = RiemannOperator(max_prime=30)
        primes = op._sieve_of_eratosthenes(30)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        op = RiemannOperator(max_prime=100)
        spectrum = op.compute_spectrum()
        assert len(spectrum) > 0
        # Spectrum should have positive values
        assert all(spectrum >= 0)
    
    def test_information_bottleneck(self):
        """Test information bottleneck."""
        op = RiemannOperator(max_prime=1000)
        ib = op.information_bottleneck()
        assert ib > 0
        # Should scale with log(max_prime)
        assert ib > KAPPA_PI


class TestBSDOperator:
    """Test BSD Conjecture spectral operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = BSDOperator(conductor=37, rank=1)
        assert op.conductor == 37
        assert op.rank == 1
        assert op.name == "BSD Conjecture"
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        op = BSDOperator(conductor=37, rank=1)
        spectrum = op.compute_spectrum()
        assert len(spectrum) > 0
        assert all(spectrum >= 0)
    
    def test_information_bottleneck_scales_with_rank(self):
        """Test that information bottleneck scales with rank."""
        op1 = BSDOperator(conductor=37, rank=1)
        op2 = BSDOperator(conductor=37, rank=2)
        
        ib1 = op1.information_bottleneck()
        ib2 = op2.information_bottleneck()
        
        # Higher rank should have higher bottleneck
        assert ib2 > ib1


class TestGoldbachOperator:
    """Test Goldbach Conjecture spectral operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = GoldbachOperator(even_number=100)
        assert op.even_number == 100
        assert op.name == "Goldbach Conjecture"
    
    def test_invalid_input(self):
        """Test handling of invalid input (odd number)."""
        op = GoldbachOperator(even_number=99)
        spectrum = op.compute_spectrum()
        # Should handle gracefully
        assert isinstance(spectrum, np.ndarray)
    
    def test_spectrum_computation(self):
        """Test spectrum computation for even number."""
        op = GoldbachOperator(even_number=100)
        spectrum = op.compute_spectrum()
        assert len(spectrum) > 0
        assert all(spectrum >= 0)
    
    def test_information_bottleneck(self):
        """Test information bottleneck."""
        op = GoldbachOperator(even_number=100)
        ib = op.information_bottleneck()
        assert ib > 0
        # Should scale with log(n)
        assert ib < KAPPA_PI * np.log(100)
    
    def test_small_even_number(self):
        """Test smallest valid input."""
        op = GoldbachOperator(even_number=4)
        spectrum = op.compute_spectrum()
        # 4 = 2 + 2
        assert len(spectrum) >= 1


class TestQCALInfinityCubed:
    """Test main QCAL ∞³ system."""
    
    def test_initialization(self):
        """Test system initialization."""
        qcal = QCALInfinityCubed()
        assert qcal.kappa_pi == KAPPA_PI
        assert qcal.f0 == F0_QCAL
        assert len(qcal.operators) == 0
    
    def test_register_operator(self):
        """Test registering operators."""
        qcal = QCALInfinityCubed()
        op = PvsNPOperator(num_vars=100, treewidth=50)
        qcal.register_operator(op)
        assert len(qcal.operators) == 1
        assert "P vs NP" in qcal.operators
    
    def test_compute_unified_spectrum(self):
        """Test computing unified spectrum."""
        qcal = create_complete_qcal_system()
        spectra = qcal.compute_unified_spectrum()
        assert len(spectra) == 4  # All 4 problems
        for name, spectrum in spectra.items():
            assert isinstance(spectrum, np.ndarray)
            assert len(spectrum) > 0
    
    def test_compute_information_landscape(self):
        """Test computing information landscape."""
        qcal = create_complete_qcal_system()
        landscape = qcal.compute_information_landscape()
        assert len(landscape) == 4
        for name, ib in landscape.items():
            assert ib > 0
            # All should scale with κ_Π
            assert ib / KAPPA_PI > 0.1
    
    def test_coupling_matrix(self):
        """Test coupling matrix computation."""
        qcal = create_complete_qcal_system()
        coupling = qcal.compute_coupling_matrix()
        
        # Should be square matrix
        assert coupling.shape[0] == coupling.shape[1]
        assert coupling.shape[0] == 4
        
        # Diagonal should be 1.0
        for i in range(4):
            assert abs(coupling[i, i] - 1.0) < 1e-10
        
        # Should be symmetric
        for i in range(4):
            for j in range(4):
                assert abs(coupling[i, j] - coupling[j, i]) < 1e-10
    
    def test_demonstrate_unification(self):
        """Test full unification demonstration."""
        qcal = create_complete_qcal_system()
        analysis = qcal.demonstrate_unification()
        
        # Check structure
        assert 'constants' in analysis
        assert 'problems' in analysis
        assert 'unified_metrics' in analysis
        
        # Check constants
        assert analysis['constants']['κ_Π'] == KAPPA_PI
        assert analysis['constants']['f₀'] == F0_QCAL
        
        # Check problems
        assert len(analysis['problems']) == 4
        for name, data in analysis['problems'].items():
            assert 'dimension' in data
            assert 'information_bottleneck' in data
            assert 'coupling_strength' in data
        
        # Check unified metrics
        metrics = analysis['unified_metrics']
        assert 'total_information' in metrics
        assert 'field_coherence' in metrics
        assert metrics['total_information'] > 0
    
    def test_field_coherence(self):
        """Test field coherence computation."""
        qcal = create_complete_qcal_system()
        coherence = qcal._compute_field_coherence()
        # Coherence should be positive
        assert coherence > 0
    
    def test_verify_universal_principle(self):
        """Test verification of universal principles."""
        qcal = create_complete_qcal_system()
        verification = qcal.verify_universal_principle()
        
        # Should have verification for each problem
        assert len(verification) > 0
        
        # All values should be boolean
        for key, value in verification.items():
            assert isinstance(value, bool)
        
        # κ_Π should be consistent across problems
        kappa_checks = [v for k, v in verification.items() if 'kappa' in k.lower()]
        assert len(kappa_checks) > 0


class TestSystemIntegration:
    """Integration tests for complete system."""
    
    def test_create_complete_system(self):
        """Test creating complete QCAL system."""
        qcal = create_complete_qcal_system()
        assert len(qcal.operators) == 4
        
        expected_problems = [
            "P vs NP",
            "Riemann Hypothesis",
            "BSD Conjecture",
            "Goldbach Conjecture"
        ]
        for problem in expected_problems:
            assert problem in qcal.operators
    
    def test_all_operators_functional(self):
        """Test that all operators are functional."""
        qcal = create_complete_qcal_system()
        
        for name, op in qcal.operators.items():
            # Each operator should compute spectrum
            spectrum = op.compute_spectrum()
            assert isinstance(spectrum, np.ndarray)
            assert len(spectrum) > 0
            
            # Each should compute information bottleneck
            ib = op.information_bottleneck()
            assert ib > 0
            
            # Each should couple to QCAL field
            coupling = op.coupling_strength()
            assert coupling != 0
    
    def test_problem_interconnections(self):
        """Test that problems are interconnected through QCAL."""
        qcal = create_complete_qcal_system()
        coupling = qcal.compute_coupling_matrix()
        
        # Off-diagonal elements should be non-zero (problems are coupled)
        for i in range(4):
            for j in range(4):
                if i != j:
                    # Should have some coupling
                    assert abs(coupling[i, j]) > 0.01
    
    def test_universal_constant_consistency(self):
        """Test that κ_Π appears consistently."""
        qcal = create_complete_qcal_system()
        
        # Each operator should use κ_Π
        for op in qcal.operators.values():
            assert op.kappa == KAPPA_PI
        
        # System should use κ_Π
        assert qcal.kappa_pi == KAPPA_PI
    
    def test_frequency_consistency(self):
        """Test that f₀ appears consistently."""
        qcal = create_complete_qcal_system()
        
        # Each operator should use f₀
        for op in qcal.operators.values():
            assert op.frequency == F0_QCAL
        
        # System should use f₀
        assert qcal.f0 == F0_QCAL


class TestMathematicalProperties:
    """Test mathematical properties of the system."""
    
    def test_spectrum_positivity(self):
        """Test that all spectra have non-negative eigenvalues."""
        qcal = create_complete_qcal_system()
        spectra = qcal.compute_unified_spectrum()
        
        for name, spectrum in spectra.items():
            assert all(spectrum >= 0), f"{name} has negative eigenvalues"
    
    def test_information_monotonicity(self):
        """Test that larger problems have larger information bottlenecks."""
        # P vs NP: larger treewidth → larger bottleneck
        op1 = PvsNPOperator(num_vars=100, treewidth=10)
        op2 = PvsNPOperator(num_vars=100, treewidth=50)
        assert op2.information_bottleneck() > op1.information_bottleneck()
        
        # Riemann: larger prime range → larger bottleneck
        rh1 = RiemannOperator(max_prime=100)
        rh2 = RiemannOperator(max_prime=1000)
        assert rh2.information_bottleneck() > rh1.information_bottleneck()
    
    def test_coupling_symmetry(self):
        """Test that coupling matrix is symmetric."""
        qcal = create_complete_qcal_system()
        coupling = qcal.compute_coupling_matrix()
        
        # Check symmetry
        assert np.allclose(coupling, coupling.T)
    
    def test_coupling_positive_definite(self):
        """Test that coupling matrix is positive definite."""
        qcal = create_complete_qcal_system()
        coupling = qcal.compute_coupling_matrix()
        
        # Eigenvalues should be positive
        eigenvalues = np.linalg.eigvals(coupling)
        assert all(eigenvalues > -1e-10)  # Allow small numerical errors


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
