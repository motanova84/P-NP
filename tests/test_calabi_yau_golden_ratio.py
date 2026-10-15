"""
Test suite for Calabi-Yau Golden Ratio Analysis
================================================

Tests the golden ratio analyzer that explores relationships between
Calabi-Yau Hodge numbers and the golden ratio squared (φ²).

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_golden_ratio_analysis import GoldenRatioAnalyzer


class TestGoldenRatioAnalyzer:
    """Test suite for the Golden Ratio Analyzer."""
    
    def test_initialization(self):
        """Test that analyzer initializes with correct golden ratio values."""
        analyzer = GoldenRatioAnalyzer()
        
        # φ = (1 + √5) / 2 ≈ 1.618033988749895
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(analyzer.phi - expected_phi) < 1e-10
        
        # φ² ≈ 2.618033988749895
        expected_phi_squared = expected_phi ** 2
        assert abs(analyzer.phi_squared - expected_phi_squared) < 1e-10
        assert abs(analyzer.phi_squared - 2.618033988749895) < 1e-10
    
    def test_generate_hodge_pairs(self):
        """Test generation of Hodge number pairs."""
        analyzer = GoldenRatioAnalyzer()
        
        # Test with small max_n
        pairs = analyzer.generate_hodge_pairs(max_n=5)
        
        # Verify structure: (N, h11, h21, ratio, difference)
        assert len(pairs) > 0
        for pair in pairs:
            assert len(pair) == 5
            N, h11, h21, ratio, diff = pair
            
            # Check N = h11 + h21
            assert N == h11 + h21
            
            # Check positive values
            assert h11 > 0
            assert h21 > 0
            assert N >= 3  # Minimum N is 3
            assert N <= 5  # Maximum N is 5
            
            # Check ratio calculation
            assert abs(ratio - (h11 / h21)) < 1e-10
            
            # Check difference calculation
            assert abs(diff - abs(ratio - analyzer.phi_squared)) < 1e-10
    
    def test_find_closest_to_phi_squared(self):
        """Test finding pairs closest to φ²."""
        analyzer = GoldenRatioAnalyzer()
        
        # Find top 10 with N ≤ 50
        top_10 = analyzer.find_closest_to_phi_squared(max_n=50, top_k=10)
        
        # Should return exactly 10 results
        assert len(top_10) == 10
        
        # First result should be (47, 34, 13) as per problem statement
        N, h11, h21, ratio, diff = top_10[0]
        assert N == 47
        assert h11 == 34
        assert h21 == 13
        
        # Verify the ratio is close to φ²
        assert abs(ratio - 2.6153846153846154) < 1e-10
        
        # Verify the difference is minimal
        assert diff < 0.003  # Should be ~0.0026493734
        
        # Results should be sorted by difference (ascending)
        differences = [pair[4] for pair in top_10]
        assert differences == sorted(differences)
    
    def test_expected_top_10_results(self):
        """Test that we get the exact expected top 10 results."""
        analyzer = GoldenRatioAnalyzer()
        top_10 = analyzer.find_closest_to_phi_squared(max_n=50, top_k=10)
        
        # Expected results from problem statement
        expected = [
            (47, 34, 13),
            (29, 21, 8),
            (18, 13, 5),
            (36, 26, 10),
            (40, 29, 11),
            (43, 31, 12),
            (25, 18, 7),
            (50, 36, 14),
            (11, 8, 3),
            (22, 16, 6)
        ]
        
        # Verify each result
        for i, (expected_N, expected_h11, expected_h21) in enumerate(expected):
            N, h11, h21, ratio, diff = top_10[i]
            assert N == expected_N
            assert h11 == expected_h11
            assert h21 == expected_h21
    
    def test_format_results_table(self):
        """Test that results can be formatted as a table."""
        analyzer = GoldenRatioAnalyzer()
        top_10 = analyzer.find_closest_to_phi_squared(max_n=50, top_k=10)
        
        # Format as table
        table = analyzer.format_results_table(top_10)
        
        # Should be a non-empty string
        assert isinstance(table, str)
        assert len(table) > 0
        
        # Should contain key information
        assert "φ" in table or "phi" in table.lower()
        assert "GOLDEN RATIO" in table
        assert "HODGE" in table
        assert "34" in table  # Best h11 value
        assert "13" in table  # Best h21 value
    
    def test_analyze_convergence(self):
        """Test convergence statistics calculation."""
        analyzer = GoldenRatioAnalyzer()
        top_10 = analyzer.find_closest_to_phi_squared(max_n=50, top_k=10)
        
        # Get statistics
        stats = analyzer.analyze_convergence(top_10)
        
        # Check that all expected keys are present
        assert 'min_difference' in stats
        assert 'max_difference' in stats
        assert 'mean_difference' in stats
        assert 'std_difference' in stats
        assert 'min_ratio' in stats
        assert 'max_ratio' in stats
        assert 'mean_ratio' in stats
        assert 'N_range' in stats
        assert 'total_pairs_analyzed' in stats
        
        # Verify some values
        assert stats['total_pairs_analyzed'] == 10
        assert stats['min_difference'] < stats['max_difference']
        assert stats['N_range'][0] <= stats['N_range'][1]
        
        # The minimum difference should be from the best approximation
        assert stats['min_difference'] < 0.003
    
    def test_fibonacci_relationship(self):
        """Test that top results show Fibonacci-like properties."""
        analyzer = GoldenRatioAnalyzer()
        top_10 = analyzer.find_closest_to_phi_squared(max_n=50, top_k=10)
        
        # The best approximation (34, 13) contains Fibonacci numbers
        # 34 and 13 are consecutive Fibonacci numbers!
        N, h11, h21, ratio, diff = top_10[0]
        
        # Check if they are Fibonacci numbers
        fib_sequence = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
        assert h11 in fib_sequence  # 34 is Fibonacci
        assert h21 in fib_sequence  # 13 is Fibonacci
        
        # In the Fibonacci sequence, 34/13 should be close to φ²
        # This validates the mathematical connection
        assert diff < 0.003
    
    def test_different_max_n_values(self):
        """Test analyzer with different maximum N values."""
        analyzer = GoldenRatioAnalyzer()
        
        # Test with smaller max_n
        top_5_small = analyzer.find_closest_to_phi_squared(max_n=20, top_k=5)
        assert len(top_5_small) == 5
        
        # All N values should be ≤ 20
        for N, h11, h21, ratio, diff in top_5_small:
            assert N <= 20
        
        # Test with larger max_n
        top_5_large = analyzer.find_closest_to_phi_squared(max_n=100, top_k=5)
        assert len(top_5_large) == 5
        
        # Should potentially find better approximations
        # (or at least as good) with larger search space
        best_diff_small = top_5_small[0][4]
        best_diff_large = top_5_large[0][4]
        assert best_diff_large <= best_diff_small


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
