#!/usr/bin/env python3
"""
Tests for kappa_pi_distribution module
======================================

Tests the computation and analysis of κ_Π distribution for Calabi-Yau manifolds.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 enero 2026
"""

import pytest
import numpy as np
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.kappa_pi_distribution import (
    compute_kappa_distribution,
    analyze_local_density,
    compare_with_theoretical_distribution
)


class TestComputeKappaDistribution:
    """Tests for compute_kappa_distribution function"""
    
    def test_simple_case(self):
        """Test with simple known values"""
        cy_list = [(4, 4), (8, 8), (16, 16)]  # N = 8, 16, 32
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        # Check Ns
        assert Ns == [8, 16, 32]
        
        # Check kappas (log2 values)
        assert abs(kappas[0] - 3.0) < 1e-10
        assert abs(kappas[1] - 4.0) < 1e-10
        assert abs(kappas[2] - 5.0) < 1e-10
        
        # Check stats
        assert stats['total_manifolds'] == 3
        assert abs(stats['mean'] - 4.0) < 1e-10
        assert stats['min'] == 3.0
        assert stats['max'] == 5.0
    
    def test_N13_detection(self):
        """Test detection of N=13 cases"""
        cy_list = [
            (7, 6),   # N = 13
            (10, 3),  # N = 13
            (5, 5),   # N = 10
            (2, 11),  # N = 13
        ]
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        # Should detect 3 cases with N=13
        assert stats['special_N13_count'] == 3
        assert abs(stats['special_N13_kappa'] - math.log2(13)) < 1e-10
        assert abs(stats['density_N13'] - 0.75) < 1e-10
    
    def test_empty_list(self):
        """Test with empty list"""
        cy_list = []
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        assert len(kappas) == 0
        assert len(Ns) == 0
        assert stats['total_manifolds'] == 0
        assert stats['density_N13'] == 0.0
        assert np.isnan(stats['mean'])
        assert np.isnan(stats['std'])
    
    def test_different_base(self):
        """Test with different logarithm base"""
        cy_list = [(5, 5)]  # N = 10
        
        # Base 2
        kappas_2, _, _ = compute_kappa_distribution(cy_list, base=2)
        assert abs(kappas_2[0] - math.log2(10)) < 1e-10
        
        # Base e
        kappas_e, _, _ = compute_kappa_distribution(cy_list, base=math.e)
        assert abs(kappas_e[0] - math.log(10)) < 1e-10
        
        # Base 10
        kappas_10, _, _ = compute_kappa_distribution(cy_list, base=10)
        assert abs(kappas_10[0] - 1.0) < 1e-10
    
    def test_statistics_calculation(self):
        """Test statistical calculations"""
        # Known distribution
        cy_list = [(1, 1), (2, 2), (4, 4), (8, 8), (16, 16)]
        # N = 2, 4, 8, 16, 32
        # κ = 1, 2, 3, 4, 5
        
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        # Mean should be 3.0
        assert abs(stats['mean'] - 3.0) < 1e-10
        
        # Median should be 3.0
        assert abs(stats['median'] - 3.0) < 1e-10
        
        # Min and max
        assert stats['min'] == 1.0
        assert stats['max'] == 5.0
        
        # Standard deviation
        expected_std = np.std([1.0, 2.0, 3.0, 4.0, 5.0])
        assert abs(stats['std'] - expected_std) < 1e-10


class TestAnalyzeLocalDensity:
    """Tests for analyze_local_density function"""
    
    def test_exact_count(self):
        """Test exact count of target N"""
        Ns = [10, 13, 13, 13, 20, 25]
        result = analyze_local_density(Ns, target_N=13)
        
        assert result['exact_count'] == 3
        assert result['target_N'] == 13
        assert result['total_manifolds'] == 6
    
    def test_window_count(self):
        """Test window counting"""
        Ns = [10, 11, 12, 13, 14, 15, 20]
        result = analyze_local_density(Ns, target_N=13, window=2)
        
        # Window [11-15] should include all except 10 and 20
        assert result['window_count'] == 5
    
    def test_density_calculation(self):
        """Test density calculation"""
        Ns = [13, 13, 20, 25]
        result = analyze_local_density(Ns, target_N=13)
        
        # 2 out of 4 = 0.5
        assert abs(result['exact_density'] - 0.5) < 1e-10
    
    def test_anomaly_detection(self):
        """Test anomaly detection"""
        # Create distribution where N=13 is anomalously common relative to expected
        # Small mean with lots of N=13
        Ns = [13] * 30 + [30, 35, 40, 45, 50] * 2  # mean ~21
        result = analyze_local_density(Ns, target_N=13)
        
        # 30/40 = 0.75, expected ~0.52 (exp(-13/21)), ratio ~1.45x
        assert result['exact_count'] == 30
        assert result['anomaly_ratio'] > 1.4
    
    def test_no_anomaly(self):
        """Test when there is no anomaly"""
        # Exponentially distributed
        Ns = [5, 10, 15, 20, 25, 30, 40, 50, 100, 200]
        result = analyze_local_density(Ns, target_N=13)
        
        # Should not be anomalous
        assert result['is_anomalous'] == False


class TestCompareWithTheoretical:
    """Tests for compare_with_theoretical_distribution function"""
    
    def test_exponential_model(self):
        """Test exponential model comparison"""
        # Generate exponentially distributed data
        np.random.seed(42)
        mean_N = 50
        Ns = np.random.exponential(scale=mean_N, size=100).astype(int) + 1
        Ns = [int(n) for n in Ns]
        
        result = compare_with_theoretical_distribution(Ns, model='exponential')
        
        assert result['model'] == 'exponential'
        assert 'alpha' in result
        assert 'chi_squared' in result
        assert result['alpha'] > 0
        
        # Alpha should be approximately 1/mean_N
        # (may vary due to random sampling)
        assert 0.01 < result['alpha'] < 0.1
    
    def test_lognormal_model(self):
        """Test lognormal model comparison"""
        # Generate lognormal distributed data
        np.random.seed(42)
        Ns = np.random.lognormal(mean=3.0, sigma=1.0, size=100).astype(int) + 1
        Ns = [int(n) for n in Ns]
        
        result = compare_with_theoretical_distribution(Ns, model='lognormal')
        
        assert result['model'] == 'lognormal'
        assert 'mu' in result
        assert 'sigma' in result
        assert result['mu'] > 0
        assert result['sigma'] > 0
    
    def test_invalid_model(self):
        """Test with invalid model name"""
        Ns = [10, 20, 30]
        
        with pytest.raises(ValueError, match="Modelo desconocido"):
            compare_with_theoretical_distribution(Ns, model='invalid')


class TestIntegration:
    """Integration tests for the full workflow"""
    
    def test_full_workflow(self):
        """Test complete analysis workflow"""
        # Generate realistic test data
        np.random.seed(42)
        cy_list = []
        
        # Regular cases
        for _ in range(90):
            h11 = np.random.randint(1, 100)
            h21 = np.random.randint(1, 100)
            cy_list.append((h11, h21))
        
        # Special cases with N=13
        for _ in range(10):
            h11 = np.random.randint(1, 13)
            h21 = 13 - h11
            cy_list.append((h11, h21))
        
        # 1. Compute distribution
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        assert len(kappas) == 100
        assert len(Ns) == 100
        assert stats['total_manifolds'] == 100
        
        # 2. Analyze local density
        density = analyze_local_density(Ns, target_N=13)
        
        # Should have detected the 10 special cases
        assert density['exact_count'] >= 10
        assert density['exact_density'] >= 0.1
        
        # 3. Compare with theoretical
        exp_result = compare_with_theoretical_distribution(Ns, model='exponential')
        assert exp_result['alpha'] > 0
        
        lognorm_result = compare_with_theoretical_distribution(Ns, model='lognormal')
        assert lognorm_result['mu'] > 0
    
    def test_edge_case_single_manifold(self):
        """Test with single manifold"""
        cy_list = [(7, 6)]  # N = 13
        
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        assert len(kappas) == 1
        assert stats['special_N13_count'] == 1
        assert stats['density_N13'] == 1.0
        assert stats['mean'] == stats['median']
        assert stats['std'] == 0.0
    
    def test_numerical_stability(self):
        """Test numerical stability with extreme values"""
        cy_list = [
            (1, 1),      # N = 2 (small)
            (250, 250),  # N = 500 (large)
        ]
        
        kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
        
        # Should handle without errors
        assert len(kappas) == 2
        assert all(k > 0 for k in kappas)
        assert not np.isnan(stats['mean'])
        assert not np.isinf(stats['mean'])


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
