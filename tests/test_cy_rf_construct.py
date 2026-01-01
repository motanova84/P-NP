#!/usr/bin/env python3
"""
test_cy_rf_construct.py - Tests for CY-RF-CONSTRUCT problem

Tests the Calabi-Yau Ricci-Flat metric construction complexity framework.

© JMMB | P vs NP Verification System
"""

import pytest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from cy_rf_construct import (
    CalabiYauManifold,
    SpectralComplexityMeasure,
    CYRFConstructProblem,
    ConditionalHardness,
    ExperimentalValidation
)


class TestCalabiYauManifold:
    """Tests for CalabiYauManifold dataclass."""
    
    def test_basic_creation(self):
        """Test basic manifold creation."""
        m = CalabiYauManifold(h_11=1, h_21=101, name="Quintic")
        assert m.h_11 == 1
        assert m.h_21 == 101
        assert m.name == "Quintic"
    
    def test_euler_characteristic(self):
        """Test Euler characteristic computation."""
        m = CalabiYauManifold(h_11=1, h_21=101)
        assert m.euler_char == 2 * (1 - 101)
        assert m.euler_char == -200
        
        # Self-mirror case
        m2 = CalabiYauManifold(h_11=19, h_21=19)
        assert m2.euler_char == 0
    
    def test_total_moduli(self):
        """Test total moduli dimension."""
        m = CalabiYauManifold(h_11=1, h_21=101)
        assert m.total_moduli == 102
        
        m2 = CalabiYauManifold(h_11=4, h_21=4)
        assert m2.total_moduli == 8
    
    def test_negative_hodge_numbers_rejected(self):
        """Test that negative Hodge numbers raise error."""
        with pytest.raises(ValueError):
            CalabiYauManifold(h_11=-1, h_21=10)
        
        with pytest.raises(ValueError):
            CalabiYauManifold(h_11=10, h_21=-1)


class TestSpectralComplexityMeasure:
    """Tests for spectral complexity measure κ_Π."""
    
    def test_kappa_pi_basic(self):
        """Test basic κ_Π computation."""
        m = CalabiYauManifold(h_11=1, h_21=101)
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        
        # κ_Π = log₂(1 + 101) = log₂(102)
        expected = math.log2(102)
        assert abs(kappa - expected) < 1e-10
    
    def test_kappa_pi_special_values(self):
        """Test κ_Π for special cases."""
        # log₂(13) ≈ 3.700 (mentioned in problem statement)
        m = CalabiYauManifold(h_11=6, h_21=7)  # total = 13
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        assert abs(kappa - math.log2(13)) < 1e-10
        assert abs(kappa - 3.700) < 0.001
        
        # Power of 2
        m2 = CalabiYauManifold(h_11=8, h_21=8)  # total = 16 = 2^4
        kappa2 = SpectralComplexityMeasure.kappa_pi(m2)
        assert abs(kappa2 - 4.0) < 1e-10
    
    def test_kappa_pi_zero_moduli(self):
        """Test edge case with zero moduli."""
        m = CalabiYauManifold(h_11=0, h_21=0)
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        assert kappa == 0.0
    
    def test_moduli_space_size(self):
        """Test Theorem 5.1: |M_X| ≥ 2^κ_Π."""
        m = CalabiYauManifold(h_11=1, h_21=101)
        size = SpectralComplexityMeasure.moduli_space_size(m)
        
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        expected_size = 2 ** int(kappa)
        
        assert size == expected_size
        assert size >= 2 ** int(kappa)
    
    def test_monotonicity_property(self):
        """Test Proposition 4.2: monotonicity of κ_Π."""
        m1 = CalabiYauManifold(h_11=1, h_21=1)    # total = 2
        m2 = CalabiYauManifold(h_11=5, h_21=5)    # total = 10
        m3 = CalabiYauManifold(h_11=10, h_21=10)  # total = 20
        
        kappa1 = SpectralComplexityMeasure.kappa_pi(m1)
        kappa2 = SpectralComplexityMeasure.kappa_pi(m2)
        kappa3 = SpectralComplexityMeasure.kappa_pi(m3)
        
        # More moduli → higher κ_Π
        assert kappa1 < kappa2 < kappa3
        
        # Verify using is_monotone method
        assert SpectralComplexityMeasure.is_monotone(m1, m2)
        assert SpectralComplexityMeasure.is_monotone(m2, m3)
        assert SpectralComplexityMeasure.is_monotone(m1, m3)


class TestCYRFConstructProblem:
    """Tests for CY-RF-CONSTRUCT problem."""
    
    def test_problem_creation(self):
        """Test problem instance creation."""
        m = CalabiYauManifold(h_11=1, h_21=101, name="Quintic")
        epsilon = 0.001
        
        problem = CYRFConstructProblem(m, epsilon)
        assert problem.manifold == m
        assert problem.epsilon == epsilon
    
    def test_is_in_np(self):
        """Test Lemma 3.2: CY-RF-CONSTRUCT ∈ NP."""
        m = CalabiYauManifold(h_11=1, h_21=101)
        problem = CYRFConstructProblem(m, 0.01)
        
        is_np, explanation = problem.is_in_np()
        
        assert is_np == True
        assert "NP" in explanation
        assert "Certificate" in explanation
        assert "polynomial" in explanation
    
    def test_search_space_complexity(self):
        """Test Section 5: search space complexity analysis."""
        m = CalabiYauManifold(h_11=4, h_21=4)
        problem = CYRFConstructProblem(m, 0.01)
        
        complexity = problem.get_search_space_complexity()
        
        assert 'kappa_pi' in complexity
        assert 'min_moduli_space_size' in complexity
        assert 'min_search_time_exponential' in complexity
        assert complexity['total_moduli_dim'] == 8
        assert complexity['h_11'] == 4
        assert complexity['h_21'] == 4
        
        # Verify exponential relationship
        kappa = complexity['kappa_pi']
        exp_time = complexity['min_search_time_exponential']
        assert abs(exp_time - 2**kappa) < 1e-6
    
    def test_corollary_5_2_exponential_time(self):
        """Test Corollary 5.2: exponential time requirement."""
        m = CalabiYauManifold(h_11=10, h_21=10)
        problem = CYRFConstructProblem(m, 0.001)
        
        complexity = problem.get_search_space_complexity()
        
        # Without structure, time exponential in κ_Π
        kappa = complexity['kappa_pi']
        assert kappa > 0
        assert complexity['min_search_time_exponential'] == 2**kappa
        
        # For 20 total moduli, κ_Π ≈ log₂(20) ≈ 4.32
        assert kappa > 4.0
        assert complexity['min_search_time_exponential'] > 16


class TestConditionalHardness:
    """Tests for conditional hardness framework (Section 6)."""
    
    def test_analyze_reduction(self):
        """Test SAT → CY-RF-CONSTRUCT reduction analysis."""
        sat_vars = 100
        reduction = ConditionalHardness.analyze_reduction(sat_vars)
        
        assert reduction['sat_variables'] == sat_vars
        assert reduction['cy_total_moduli'] == sat_vars
        assert reduction['reduction_polynomial'] == True
        assert reduction['implies_p_eq_np_if_in_p'] == True
        
        # Verify κ_Π computed correctly
        expected_kappa = math.log2(sat_vars)
        assert abs(reduction['kappa_pi'] - expected_kappa) < 1e-6
    
    def test_theorem_6_2_statement(self):
        """Test Theorem 6.2 statement generation."""
        statement = ConditionalHardness.theorem_6_2_implication()
        
        assert "Theorem 6.2" in statement
        assert "Conditional" in statement
        assert "CY-RF-CONSTRUCT ∈ P ⟹ P = NP" in statement
        assert "Proof Sketch" in statement
        assert "spectral barrier" in statement
    
    def test_reduction_different_sizes(self):
        """Test reduction for different SAT instance sizes."""
        sizes = [10, 50, 100, 200]
        
        for size in sizes:
            reduction = ConditionalHardness.analyze_reduction(size)
            
            # Total moduli should match SAT vars
            assert reduction['cy_total_moduli'] == size
            
            # κ_Π should increase with size
            kappa = reduction['kappa_pi']
            assert kappa == math.log2(size)


class TestExperimentalValidation:
    """Tests for experimental validation (Section 8)."""
    
    def test_create_sample_database(self):
        """Test creation of Kreuzer-Skarke sample."""
        manifolds = ExperimentalValidation.create_kreuzer_skarke_sample()
        
        assert len(manifolds) > 0
        assert all(isinstance(m, CalabiYauManifold) for m in manifolds)
        
        # Check specific known manifolds
        quintic = next((m for m in manifolds if "Quintic" in m.name), None)
        assert quintic is not None
        assert quintic.h_11 == 1
        assert quintic.h_21 == 101
    
    def test_compute_statistics(self):
        """Test statistical analysis of κ_Π."""
        manifolds = ExperimentalValidation.create_kreuzer_skarke_sample()
        stats = ExperimentalValidation.compute_statistics(manifolds)
        
        assert stats['num_manifolds'] == len(manifolds)
        assert 'kappa_pi_mean' in stats
        assert 'kappa_pi_std' in stats
        assert 'kappa_pi_min' in stats
        assert 'kappa_pi_max' in stats
        
        # Mean should be positive
        assert stats['kappa_pi_mean'] > 0
        
        # Min should be less than max
        assert stats['kappa_pi_min'] <= stats['kappa_pi_max']
        
        # Check special value log₂(13)
        assert abs(stats['special_value_log2_13'] - 3.700) < 0.001
    
    def test_statistics_kappa_values(self):
        """Test that κ_Π values are computed for all manifolds."""
        manifolds = ExperimentalValidation.create_kreuzer_skarke_sample()
        stats = ExperimentalValidation.compute_statistics(manifolds)
        
        kappa_values = stats['kappa_values']
        
        assert len(kappa_values) == len(manifolds)
        assert all(k > 0 for k in kappa_values)
        
        # Verify values match individual computations
        for m, k in zip(manifolds, kappa_values):
            expected = SpectralComplexityMeasure.kappa_pi(m)
            assert abs(k - expected) < 1e-10


class TestIntegration:
    """Integration tests for complete framework."""
    
    def test_complete_workflow(self):
        """Test complete workflow from problem statement."""
        # 1. Define manifold
        quintic = CalabiYauManifold(h_11=1, h_21=101, name="Quintic")
        
        # 2. Create problem instance
        epsilon = 0.001
        problem = CYRFConstructProblem(quintic, epsilon)
        
        # 3. Verify in NP
        is_np, _ = problem.is_in_np()
        assert is_np
        
        # 4. Compute κ_Π
        kappa = SpectralComplexityMeasure.kappa_pi(quintic)
        assert kappa > 0
        
        # 5. Analyze search space
        complexity = problem.get_search_space_complexity()
        assert complexity['kappa_pi'] == kappa
        
        # 6. Verify exponential barrier
        assert complexity['min_search_time_exponential'] > 0
    
    def test_special_value_log2_13(self):
        """Test special case κ_Π = log₂(13) ≈ 3.700."""
        # Create manifold with total moduli = 13
        m = CalabiYauManifold(h_11=6, h_21=7)
        assert m.total_moduli == 13
        
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        assert abs(kappa - 3.700) < 0.001
        assert abs(kappa - math.log2(13)) < 1e-10
        
        # Create problem and verify complexity
        problem = CYRFConstructProblem(m, 0.01)
        complexity = problem.get_search_space_complexity()
        
        assert abs(complexity['kappa_pi'] - 3.700) < 0.001
    
    def test_framework_consistency(self):
        """Test consistency across all framework components."""
        manifolds = ExperimentalValidation.create_kreuzer_skarke_sample()
        
        for m in manifolds:
            # κ_Π should be well-defined
            kappa = SpectralComplexityMeasure.kappa_pi(m)
            assert kappa >= 0
            
            # Moduli space size should follow theorem
            size = SpectralComplexityMeasure.moduli_space_size(m)
            assert size >= 2 ** int(kappa)
            
            # Problem should be in NP
            problem = CYRFConstructProblem(m, 0.01)
            is_np, _ = problem.is_in_np()
            assert is_np


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
