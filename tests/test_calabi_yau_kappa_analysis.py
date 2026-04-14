#!/usr/bin/env python3
"""
test_calabi_yau_kappa_analysis.py - Tests for Calabi-Yau κ_Π Analysis

Test suite for the Calabi-Yau κ_Π analysis module with custom logarithmic base.

© JMMB | P vs NP Verification System
"""

import sys
import os
import pytest
import numpy as np
import pandas as pd

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_kappa_analysis import (
    load_cy_data,
    compute_kappa_custom_base,
    analyze_kappa_distribution,
    run_analysis
)


class TestLoadCYData:
    """Test suite for loading Calabi-Yau data."""
    
    def test_load_cy_data_returns_dataframe(self):
        """Test that load_cy_data returns a DataFrame."""
        df = load_cy_data()
        assert isinstance(df, pd.DataFrame)
    
    def test_load_cy_data_has_correct_columns(self):
        """Test that the DataFrame has required columns."""
        df = load_cy_data()
        assert 'name' in df.columns
        assert 'h11' in df.columns
        assert 'h21' in df.columns
    
    def test_load_cy_data_has_20_varieties(self):
        """Test that we have exactly 20 Calabi-Yau varieties."""
        df = load_cy_data()
        assert len(df) == 20
    
    def test_load_cy_data_contains_quintic(self):
        """Test that the dataset includes the Quintic variety."""
        df = load_cy_data()
        quintic = df[df['name'] == 'Quintic']
        assert len(quintic) == 1
        assert quintic.iloc[0]['h11'] == 1
        assert quintic.iloc[0]['h21'] == 101
    
    def test_load_cy_data_hodge_numbers_non_negative(self):
        """Test that all Hodge numbers are non-negative."""
        df = load_cy_data()
        assert (df['h11'] >= 0).all()
        assert (df['h21'] >= 0).all()


class TestComputeKappaCustomBase:
    """Test suite for computing κ_Π with custom base."""
    
    def test_compute_adds_N_column(self):
        """Test that compute function adds N column."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        assert 'N' in df_result.columns
    
    def test_compute_adds_kappa_custom_column(self):
        """Test that compute function adds kappa_custom column."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        assert 'kappa_custom' in df_result.columns
    
    def test_N_equals_h11_plus_h21(self):
        """Test that N = h11 + h21."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        assert (df_result['N'] == df_result['h11'] + df_result['h21']).all()
    
    def test_kappa_custom_calculation_base_2(self):
        """Test κ_custom calculation with base 2."""
        df = pd.DataFrame({'name': ['Test'], 'h11': [5], 'h21': [3]})
        df_result = compute_kappa_custom_base(df, 2.0)
        # N = 8, log_2(8) = 3
        assert abs(df_result['kappa_custom'].iloc[0] - 3.0) < 1e-10
    
    def test_kappa_custom_calculation_base_e(self):
        """Test κ_custom calculation with base e."""
        df = pd.DataFrame({'name': ['Test'], 'h11': [0], 'h21': [np.e]})
        df_result = compute_kappa_custom_base(df, np.e)
        # N = e, log_e(e) = 1
        assert abs(df_result['kappa_custom'].iloc[0] - 1.0) < 1e-10
    
    def test_kappa_custom_with_base_27069(self):
        """Test κ_custom calculation with base 2.7069."""
        df = load_cy_data()
        base_b = 2.7069
        df_result = compute_kappa_custom_base(df, base_b)
        
        # Verify calculation for each row
        for idx, row in df_result.iterrows():
            expected = np.log(row['N']) / np.log(base_b)
            assert abs(row['kappa_custom'] - expected) < 1e-10
    
    def test_quintic_kappa_value(self):
        """Test κ_custom value for the Quintic variety."""
        df = load_cy_data()
        base_b = 2.7069
        df_result = compute_kappa_custom_base(df, base_b)
        
        quintic = df_result[df_result['name'] == 'Quintic']
        N_quintic = 1 + 101  # = 102
        expected_kappa = np.log(N_quintic) / np.log(base_b)
        
        assert abs(quintic.iloc[0]['kappa_custom'] - expected_kappa) < 1e-10


class TestAnalyzeKappaDistribution:
    """Test suite for statistical analysis of κ_Π distribution."""
    
    def test_analyze_returns_dict(self):
        """Test that analyze function returns a dictionary."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        assert isinstance(stats, dict)
    
    def test_analyze_has_required_keys(self):
        """Test that stats dictionary has all required keys."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        required_keys = ['mean', 'std', 'min', 'max', 'median', 'N13_count', 'N13_kappa']
        for key in required_keys:
            assert key in stats
    
    def test_mean_is_reasonable(self):
        """Test that mean κ_custom is in reasonable range."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        # Mean should be positive and reasonable
        assert stats['mean'] > 0
        assert stats['mean'] < 10  # Shouldn't be extremely large
    
    def test_std_is_positive(self):
        """Test that standard deviation is positive."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        assert stats['std'] > 0
    
    def test_min_less_than_max(self):
        """Test that min is less than max."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        assert stats['min'] < stats['max']
    
    def test_median_between_min_and_max(self):
        """Test that median is between min and max."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        assert stats['min'] <= stats['median'] <= stats['max']
    
    def test_N13_count(self):
        """Test N=13 count matches actual data."""
        df = load_cy_data()
        df_result = compute_kappa_custom_base(df, 2.7069)
        stats = analyze_kappa_distribution(df_result)
        
        # Count N=13 varieties manually
        n13_count = (df_result['N'] == 13).sum()
        assert stats['N13_count'] == n13_count
    
    def test_N13_kappa_value(self):
        """Test N=13 kappa value is close to 2.5773."""
        df = load_cy_data()
        base_b = 2.7069
        df_result = compute_kappa_custom_base(df, base_b)
        stats = analyze_kappa_distribution(df_result)
        
        if stats['N13_kappa'] is not None:
            # For N=13 with base 2.7069, κ should be close to 2.5773
            # log_2.7069(13) ≈ 2.576
            expected = np.log(13) / np.log(base_b)
            assert abs(stats['N13_kappa'] - expected) < 1e-10
            # Should be close to millennium constant
            assert abs(stats['N13_kappa'] - 2.5773) < 0.01


class TestRunAnalysis:
    """Test suite for the complete analysis function."""
    
    def test_run_analysis_returns_tuple(self):
        """Test that run_analysis returns a tuple."""
        result = run_analysis(base=2.7069, display=False)
        assert isinstance(result, tuple)
        assert len(result) == 2
    
    def test_run_analysis_returns_dataframe_and_dict(self):
        """Test that run_analysis returns DataFrame and dict."""
        df_result, stats = run_analysis(base=2.7069, display=False)
        assert isinstance(df_result, pd.DataFrame)
        assert isinstance(stats, dict)
    
    def test_run_analysis_with_default_base(self):
        """Test run_analysis with default base."""
        df_result, stats = run_analysis(display=False)
        assert len(df_result) == 20
        assert 'mean' in stats
    
    def test_run_analysis_with_custom_base(self):
        """Test run_analysis with custom base."""
        df_result, stats = run_analysis(base=10.0, display=False)
        assert len(df_result) == 20
        # Mean should be different with different base
        df_result2, stats2 = run_analysis(base=2.0, display=False)
        assert abs(stats['mean'] - stats2['mean']) > 0.1


class TestExpectedResults:
    """Test suite to verify expected results from problem statement."""
    
    def test_expected_mean_value(self):
        """Test that mean κ_Π is approximately 2.766."""
        df_result, stats = run_analysis(base=2.7069, display=False)
        # Expected mean ≈ 2.7658
        assert abs(stats['mean'] - 2.7658) < 0.01
    
    def test_expected_median_value(self):
        """Test that median is close to 2.576."""
        df_result, stats = run_analysis(base=2.7069, display=False)
        # Expected median ≈ 2.5758
        assert abs(stats['median'] - 2.5758) < 0.01
    
    def test_expected_n13_kappa(self):
        """Test that N=13 κ_Π is close to 2.576."""
        df_result, stats = run_analysis(base=2.7069, display=False)
        if stats['N13_kappa'] is not None:
            # Expected ≈ 2.5758
            assert abs(stats['N13_kappa'] - 2.5758) < 0.01
    
    def test_expected_n13_count(self):
        """Test that we have the expected number of N=13 varieties."""
        df_result, stats = run_analysis(base=2.7069, display=False)
        # From the data, we should have some N=13 varieties
        # Let's verify the count matches the data
        n13_actual = (df_result['N'] == 13).sum()
        assert stats['N13_count'] == n13_actual


def test_integration():
    """Integration test for complete workflow."""
    # Load data
    df = load_cy_data()
    assert len(df) == 20
    
    # Compute κ_Π
    base_b = 2.7069
    df_result = compute_kappa_custom_base(df, base_b)
    assert 'kappa_custom' in df_result.columns
    
    # Analyze
    stats = analyze_kappa_distribution(df_result)
    assert 'mean' in stats
    assert 'median' in stats
    
    # Verify results are reasonable
    assert stats['mean'] > 2.0
    assert stats['mean'] < 5.0
    assert stats['median'] > 2.0
    assert stats['median'] < 5.0


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Calabi-Yau κ_Π Analysis Module")
    print("=" * 70)
    print()
    
    # Run a quick verification
    df, stats = run_analysis(base=2.7069, display=True)
    
    print()
    print("Running pytest...")
    pytest.main([__file__, "-v"])
    
    print()
    print("=" * 70)
    print("Tests completed!")
    print("=" * 70)
