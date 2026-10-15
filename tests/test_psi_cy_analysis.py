#!/usr/bin/env python3
"""
Tests for Ψ_CY Analysis Module
===============================

Tests the mathematical properties and correctness of Ψ_CY calculations.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 1, 2026
"""

import pytest
import numpy as np
import pandas as pd
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from psi_cy_analysis import (
    calculate_psi_cy,
    analyze_psi_cy,
    analyze_psi_correlation,
    asymptotic_psi_cy_symmetric,
    asymptotic_psi_cy_dominated,
    golden_ratio_psi_cy,
    analyze_asymptotic_behavior,
    connection_to_kappa_pi,
    verify_symmetry_property,
    generate_sample_cy_dataset,
)


class TestPsiCYBasicCalculation:
    """Test basic Ψ_CY calculation."""
    
    def test_symmetric_case(self):
        """Test Ψ_CY for symmetric case h¹¹ = h²¹."""
        # For h¹¹ = h²¹ = k, Ψ_CY should equal log(k) - 1
        k = 10
        psi = calculate_psi_cy(k, k)
        expected = np.log(k) - 1
        assert abs(psi - expected) < 1e-10, f"Expected {expected}, got {psi}"
    
    def test_positive_hodge_numbers_required(self):
        """Test that positive Hodge numbers are required."""
        with pytest.raises(ValueError):
            calculate_psi_cy(0, 10)
        
        with pytest.raises(ValueError):
            calculate_psi_cy(10, 0)
        
        with pytest.raises(ValueError):
            calculate_psi_cy(-5, 10)
    
    def test_quintic_example(self):
        """Test known example: quintic-type CY with h¹¹=1, h²¹=12."""
        psi = calculate_psi_cy(1, 12)
        # Should be well-defined and finite
        assert np.isfinite(psi)
        assert psi > -10  # Reasonable range
        assert psi < 10


class TestMirrorSymmetry:
    """Test mirror symmetry property of Ψ_CY."""
    
    def test_symmetry_holds(self):
        """Test Ψ_CY(h¹¹, h²¹) = Ψ_CY(h²¹, h¹¹)."""
        test_cases = [
            (1, 12),
            (7, 6),
            (10, 3),
            (50, 5),
        ]
        
        for h11, h21 in test_cases:
            assert verify_symmetry_property(h11, h21), \
                f"Symmetry failed for ({h11}, {h21})"
    
    def test_symmetry_numerical(self):
        """Test symmetry numerically for various cases."""
        for h11 in [1, 5, 10, 20]:
            for h21 in [1, 5, 10, 20]:
                psi1 = calculate_psi_cy(h11, h21)
                psi2 = calculate_psi_cy(h21, h11)
                assert abs(psi1 - psi2) < 1e-10, \
                    f"Symmetry violated: Ψ({h11},{h21})={psi1} != Ψ({h21},{h11})={psi2}"


class TestAsymptoticBehavior:
    """Test asymptotic behavior of Ψ_CY."""
    
    def test_symmetric_asymptotic(self):
        """Test symmetric case: Ψ_CY(k,k) = log(k) - 1."""
        for k in [1, 10, 100, 1000]:
            psi = asymptotic_psi_cy_symmetric(k)
            expected = np.log(k) - 1
            assert abs(psi - expected) < 1e-10
    
    def test_dominated_case(self):
        """Test dominated case where h¹¹ ≫ h²¹."""
        # When h¹¹ = 100, h²¹ = 1, should be close to log(100) - 1
        psi = asymptotic_psi_cy_dominated(100, 1)
        # The approximation is: Ψ_CY ≈ log(h¹¹) - 1 when h¹¹ ≫ h²¹
        # Exact formula gives slightly different value
        assert np.isfinite(psi)
        assert psi > np.log(100) - 2  # Lower bound
        assert psi < np.log(100)      # Upper bound
    
    def test_golden_ratio_case(self):
        """Test golden ratio case."""
        phi = 1.618033988749895
        k = 10
        psi = golden_ratio_psi_cy(k, phi)
        
        # Should be well-defined
        assert np.isfinite(psi)
        
        # Verify it equals direct calculation
        psi_direct = calculate_psi_cy(phi * k, k)
        assert abs(psi - psi_direct) < 1e-10
    
    def test_analyze_asymptotic_behavior(self):
        """Test asymptotic behavior analysis function."""
        k_values = [1, 5, 10, 50]
        df = analyze_asymptotic_behavior(k_values)
        
        # Check structure
        assert len(df) == len(k_values)
        assert 'k' in df.columns
        assert 'Psi_symmetric' in df.columns
        assert 'Psi_dominated' in df.columns
        assert 'Psi_golden' in df.columns
        
        # Check values are finite
        assert df['Psi_symmetric'].notna().all()
        assert df['Psi_dominated'].notna().all()
        assert df['Psi_golden'].notna().all()


class TestConnectionToKappaPi:
    """Test connection between Ψ_CY and κ_Π."""
    
    def test_kappa_pi_calculation(self):
        """Test that κ_Π is calculated correctly."""
        h11, h21 = 7, 6
        conn = connection_to_kappa_pi(h11, h21)
        
        N = h11 + h21
        expected_kappa = np.log(N)
        
        assert abs(conn['kappa_pi'] - expected_kappa) < 1e-10
        assert conn['N'] == N
        assert conn['h11'] == h11
        assert conn['h21'] == h21
    
    def test_psi_cy_differs_from_kappa(self):
        """Test that Ψ_CY contains more information than κ_Π."""
        # Two different CY with same N should have same κ_Π but different Ψ_CY
        conn1 = connection_to_kappa_pi(1, 12)
        conn2 = connection_to_kappa_pi(6, 7)
        
        # Same N = 13
        assert conn1['N'] == conn2['N'] == 13
        
        # Same κ_Π
        assert abs(conn1['kappa_pi'] - conn2['kappa_pi']) < 1e-10
        
        # Different Ψ_CY (distributional information)
        assert abs(conn1['psi_cy'] - conn2['psi_cy']) > 0.1


class TestStatisticalAnalysis:
    """Test statistical analysis functions."""
    
    def test_generate_sample_dataset(self):
        """Test sample dataset generation."""
        df = generate_sample_cy_dataset(50, h_range=(1, 20))
        
        assert len(df) == 50
        assert 'h11' in df.columns
        assert 'h21' in df.columns
        assert 'N' in df.columns
        assert 'euler_characteristic' in df.columns
        
        # Check values are in range
        assert df['h11'].min() >= 1
        assert df['h11'].max() <= 20
        assert df['h21'].min() >= 1
        assert df['h21'].max() <= 20
    
    def test_analyze_psi_cy(self):
        """Test Ψ_CY distribution analysis."""
        df = generate_sample_cy_dataset(100)
        df_result, stats, peak = analyze_psi_cy(df)
        
        # Check that Psi_CY column was added
        assert 'Psi_CY' in df_result.columns
        
        # Check statistics
        assert 'mean' in stats
        assert 'std' in stats
        assert 'min' in stats
        assert 'max' in stats
        assert 'median' in stats
        assert 'count' in stats
        
        # Check values are reasonable
        assert stats['count'] == 100
        assert np.isfinite(stats['mean'])
        assert stats['std'] >= 0
        assert np.isfinite(peak)
    
    def test_psi_correlation(self):
        """Test correlation analysis."""
        df = generate_sample_cy_dataset(50)
        results = analyze_psi_correlation(df)
        
        # Check results structure
        assert 'correlation' in results
        assert 'r_squared' in results
        assert 'sample_size' in results
        
        # Check values are reasonable
        assert -1 <= results['correlation'] <= 1 or np.isnan(results['correlation'])
        assert results['sample_size'] == 50


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_minimum_hodge_numbers(self):
        """Test with minimum valid Hodge numbers (1, 1)."""
        psi = calculate_psi_cy(1, 1)
        expected = np.log(1) - 1  # = 0 - 1 = -1
        assert abs(psi - expected) < 1e-10
    
    def test_large_hodge_numbers(self):
        """Test with large Hodge numbers."""
        psi = calculate_psi_cy(1000, 1000)
        expected = np.log(1000) - 1
        assert abs(psi - expected) < 1e-10
    
    def test_highly_asymmetric(self):
        """Test highly asymmetric case."""
        psi = calculate_psi_cy(1000, 1)
        # Should be close to log(1000) - 1
        assert np.isfinite(psi)
        assert psi > np.log(1000) - 2
        assert psi < np.log(1000)


def test_integration():
    """Integration test: full workflow."""
    # Generate dataset
    df = generate_sample_cy_dataset(100, h_range=(1, 30))
    
    # Analyze Psi_CY
    df, stats, peak = analyze_psi_cy(df)
    
    # Test correlation
    corr = analyze_psi_correlation(df)
    
    # Verify symmetry for a few examples
    for _, row in df.head(10).iterrows():
        assert verify_symmetry_property(row['h11'], row['h21'])
    
    # Check asymptotic behavior
    asymptotic_df = analyze_asymptotic_behavior([1, 5, 10, 50])
    
    # All should complete without errors
    assert len(df) == 100
    assert len(asymptotic_df) == 4
    assert stats['count'] == 100


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
