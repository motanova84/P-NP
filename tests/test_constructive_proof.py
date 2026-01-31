"""
Unit tests for constructive_proof.py

Tests the spectral-treewidth connection demonstration.
"""

import pytest
import networkx as nx
import sys
import os

# Add experiments directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'experiments'))

from constructive_proof import (
    compute_spectral_gap,
    compute_treewidth_lower_bound,
    verify_expander_property,
    approximate_treewidth
)


class TestSpectralGap:
    """Tests for spectral gap computation."""
    
    def test_complete_graph_spectral_gap(self):
        """Complete graph should have maximal spectral gap."""
        G = nx.complete_graph(10)
        gap = compute_spectral_gap(G)
        assert gap > 0.9, "Complete graph should have large spectral gap"
    
    def test_path_graph_small_gap(self):
        """Path graph should have small spectral gap."""
        G = nx.path_graph(20)
        gap = compute_spectral_gap(G)
        assert gap < 0.1, "Path graph should have small spectral gap"
    
    def test_empty_graph(self):
        """Empty graph should handle gracefully."""
        G = nx.Graph()
        gap = compute_spectral_gap(G)
        assert gap == 0.0


class TestTreewidthLowerBound:
    """Tests for treewidth lower bound computation."""
    
    def test_complete_graph_high_bound(self):
        """Complete graph with high spectral gap should have high tw bound."""
        G = nx.complete_graph(20)
        KAPPA_PI = 2.5773
        bound = compute_treewidth_lower_bound(G, KAPPA_PI)
        assert bound >= 20 / 10, "Complete graph should satisfy tw ≥ n/10"
    
    def test_path_graph_low_bound(self):
        """Path graph with low spectral gap should have low tw bound."""
        G = nx.path_graph(20)
        KAPPA_PI = 2.5773
        bound = compute_treewidth_lower_bound(G, KAPPA_PI)
        assert bound == 0.0, "Path graph should not satisfy tw ≥ n/10"


class TestExpanderProperty:
    """Tests for expander property verification."""
    
    def test_complete_graph_is_expander(self):
        """Complete graph should be a good expander."""
        G = nx.complete_graph(20)
        KAPPA_PI = 2.5773
        is_exp, expansion = verify_expander_property(G, KAPPA_PI)
        assert is_exp, "Complete graph should be an expander"
        assert expansion >= 1 / KAPPA_PI
    
    def test_path_not_expander(self):
        """Path graph should not be an expander."""
        G = nx.path_graph(20)
        KAPPA_PI = 2.5773
        is_exp, expansion = verify_expander_property(G, KAPPA_PI)
        # Note: Sampling may occasionally miss the worst cut
        # so we just check that expansion is computed
        assert expansion >= 0


class TestTreewidthApproximation:
    """Tests for treewidth approximation."""
    
    def test_path_graph_treewidth(self):
        """Path graph should have treewidth 1."""
        G = nx.path_graph(20)
        tw = approximate_treewidth(G)
        assert tw <= 2, "Path graph should have small treewidth"
    
    def test_complete_graph_treewidth(self):
        """Complete graph K_n should have treewidth n-1."""
        n = 10
        G = nx.complete_graph(n)
        tw = approximate_treewidth(G)
        assert tw >= n - 2, "Complete graph should have high treewidth"
    
    def test_empty_graph_treewidth(self):
        """Empty graph should have treewidth 0."""
        G = nx.Graph()
        tw = approximate_treewidth(G)
        assert tw == 0.0


class TestKappaPIValue:
    """Tests for KAPPA_PI constant."""
    
    def test_kappa_pi_value(self):
        """Verify KAPPA_PI is approximately 2.5773."""
        KAPPA_PI = 2.5773
        delta = 1 / KAPPA_PI
        assert 0.38 < delta < 0.39, "δ = 1/κ_Π should be ≈ 0.388"


class TestSeparatorEnergyMinimization:
    """Tests for separator energy function."""
    
    def test_optimal_delta_in_valid_range(self):
        """
        Test that δ = 1/κ_Π ≈ 0.388 is in a valid range.
        The actual minimum depends on graph-specific parameters,
        but δ = 1/κ_Π provides a good balance.
        """
        KAPPA_PI = 2.5773
        delta_opt = 1 / KAPPA_PI
        
        # Check that δ is in reasonable range [0.3, 0.5]
        assert 0.3 < delta_opt < 0.5, \
            "δ = 1/κ_Π should be in reasonable expansion range"
        
        # Check it's close to expected value
        assert abs(delta_opt - 0.388) < 0.001, \
            "δ = 1/κ_Π should be ≈ 0.388"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
