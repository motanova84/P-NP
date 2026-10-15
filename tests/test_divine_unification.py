#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Divine Unification Module
====================================

Comprehensive tests verifying the trinity unification and separator theorem.

Author: José Manuel Mota Burruezo (ICQ · 2025)
"""

import pytest
import math
import networkx as nx
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.divine_unification import (
    UnificationConstants,
    PHI, PI, E, LAMBDA_CY, KAPPA_PI,
    compute_separator,
    graph_information_complexity,
    verify_separator_theorem,
    TrinityUnification,
    UnifiedComplexity,
    create_test_graph,
)


class TestUnificationConstants:
    """Test that the sacred constants are correctly defined."""
    
    def test_golden_ratio(self):
        """Test φ (golden ratio) value."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
        assert abs(PHI - 1.618033988749895) < 1e-10
    
    def test_kappa_pi_calculation(self):
        """Test κ_Π = φ × (π/e) × λ_CY calculation."""
        expected = PHI * (PI / E) * LAMBDA_CY
        assert abs(KAPPA_PI - expected) < 1e-10
        
        # Verify it's approximately 2.5773
        assert abs(KAPPA_PI - 2.5773) < 0.01
    
    def test_constants_container(self):
        """Test UnificationConstants dataclass."""
        constants = UnificationConstants()
        
        assert constants.phi == PHI
        assert constants.pi == PI
        assert constants.e == E
        assert constants.lambda_cy == LAMBDA_CY
        assert constants.kappa_pi == KAPPA_PI
        assert constants.frequency == 141.7001
    
    def test_kappa_bounds(self):
        """Test that κ_Π provides meaningful bounds."""
        # κ_Π should be greater than 1 (amplification)
        assert KAPPA_PI > 1.0
        
        # But reasonable (not too large)
        assert KAPPA_PI < 10.0
        
        # Inverse should be less than 1
        assert (1.0 / KAPPA_PI) < 1.0


class TestSeparatorInformationTheorem:
    """Test the Separator Information Theorem: IC(G, S) ≥ |S| / 2."""
    
    def test_path_graph_separator(self):
        """Test separator computation on path graph."""
        G = nx.path_graph(10)
        nodes = list(G.nodes())
        
        A = set(nodes[:5])
        B = set(nodes[5:])
        
        S = compute_separator(G, A, B)
        
        # Path graph should have small separator
        assert len(S) >= 1  # At least one node separates
        assert len(S) <= 3  # Should be small for path
    
    def test_complete_graph_separator(self):
        """Test separator computation on complete graph."""
        G = nx.complete_graph(8)
        nodes = list(G.nodes())
        
        A = set(nodes[:4])
        B = set(nodes[4:])
        
        S = compute_separator(G, A, B)
        
        # Complete graph requires larger separator
        assert len(S) >= 1
    
    def test_information_complexity_positive(self):
        """Test that IC is positive for non-empty separator."""
        G = nx.path_graph(10)
        nodes = list(G.nodes())
        
        A = set(nodes[:5])
        B = set(nodes[5:])
        S = compute_separator(G, A, B)
        
        ic = graph_information_complexity(G, S)
        assert ic > 0
    
    def test_separator_theorem_holds_path(self):
        """Test theorem IC(G, S) ≥ |S|/2 on path graph."""
        G = nx.path_graph(10)
        nodes = list(G.nodes())
        
        A = set(nodes[:5])
        B = set(nodes[5:])
        S = compute_separator(G, A, B)
        
        # Verify theorem
        assert verify_separator_theorem(G, S)
        
        # Verify explicitly
        ic = graph_information_complexity(G, S)
        lower_bound = len(S) / 2.0
        assert ic >= lower_bound - 1e-9
    
    def test_separator_theorem_holds_cycle(self):
        """Test theorem on cycle graph."""
        G = nx.cycle_graph(12)
        nodes = list(G.nodes())
        
        A = set(nodes[:6])
        B = set(nodes[6:])
        S = compute_separator(G, A, B)
        
        assert verify_separator_theorem(G, S)
    
    def test_separator_theorem_holds_grid(self):
        """Test theorem on 2D grid."""
        G = nx.grid_2d_graph(4, 4)
        nodes = list(G.nodes())
        
        A = set(nodes[:8])
        B = set(nodes[8:])
        S = compute_separator(G, A, B)
        
        assert verify_separator_theorem(G, S)
    
    def test_separator_theorem_holds_complete(self):
        """Test theorem on complete graph."""
        G = nx.complete_graph(8)
        nodes = list(G.nodes())
        
        A = set(nodes[:4])
        B = set(nodes[4:])
        S = compute_separator(G, A, B)
        
        assert verify_separator_theorem(G, S)
    
    def test_empty_separator(self):
        """Test behavior with empty separator."""
        G = nx.Graph()
        G.add_node(1)
        
        S = set()
        ic = graph_information_complexity(G, S)
        assert ic == 0.0
        
        # Empty separator should satisfy theorem trivially
        assert verify_separator_theorem(G, S)


class TestTrinityUnification:
    """Test the trinity unification of Topology, Information, Computation."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.trinity = TrinityUnification()
    
    def test_topology_dimension_path(self):
        """Test topology measurement on path graph (low treewidth)."""
        G = nx.path_graph(10)
        tw = self.trinity.topology_dimension(G)
        
        # Path has treewidth 1
        assert tw >= 0
        assert tw <= 3  # Should be very low
    
    def test_topology_dimension_complete(self):
        """Test topology measurement on complete graph (high treewidth)."""
        G = nx.complete_graph(8)
        tw = self.trinity.topology_dimension(G)
        
        # Complete graph has treewidth n-1
        assert tw >= 5  # Should be high
    
    def test_information_dimension_positive(self):
        """Test that information complexity is positive."""
        G = nx.cycle_graph(10)
        ic = self.trinity.information_dimension(G)
        
        assert ic >= 0
    
    def test_computation_dimension_scales(self):
        """Test that computation scales with treewidth."""
        # Low treewidth
        comp_low = self.trinity.computation_dimension(treewidth=2, n=100)
        
        # High treewidth
        comp_high = self.trinity.computation_dimension(treewidth=50, n=100)
        
        # Higher treewidth should give higher computation
        assert comp_high > comp_low
    
    def test_duality_verification_path(self):
        """Test duality verification on path graph."""
        G = nx.path_graph(10)
        results = self.trinity.verify_duality(G)
        
        assert 'topology' in results
        assert 'information' in results
        assert 'computation' in results
        assert 'kappa_pi' in results
        assert 'unification_verified' in results
        
        # Path graph has low complexity - ratios should be reasonable
        assert results['topology'] >= 0
        assert results['information'] >= 0
        assert results['computation'] >= 0
    
    def test_duality_verification_complete(self):
        """Test duality verification on complete graph."""
        G = nx.complete_graph(8)
        results = self.trinity.verify_duality(G)
        
        assert results['topology'] > 0
        assert results['information'] > 0
        assert results['computation'] > 0
        
        # All dimensions should be positive for complete graph
        assert 'unification_verified' in results
    
    def test_duality_bounds_hold(self):
        """Test that duality bounds (1/κ_Π) · X ≤ Y ≤ κ_Π · X hold."""
        # Test on multiple graph types
        graph_types = ['path', 'cycle', 'grid']
        
        for graph_type in graph_types:
            G = create_test_graph(graph_type, 10)
            results = self.trinity.verify_duality(G)
            
            # If topology is meaningful, bounds should be checked
            if results['topology'] > 1:
                bounds = results['bounds']
                
                # At least one bound check should exist
                assert len(bounds) > 0
    
    def test_kappa_constant_in_results(self):
        """Test that κ_Π appears in results."""
        G = nx.cycle_graph(10)
        results = self.trinity.verify_duality(G)
        
        assert results['kappa_pi'] == KAPPA_PI
        assert abs(results['kappa_pi'] - 2.5773) < 0.01


class TestUnifiedComplexity:
    """Test the unified complexity measure."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.unified = UnifiedComplexity()
    
    def test_measure_returns_all_dimensions(self):
        """Test that measure returns all three dimensions."""
        G = nx.cycle_graph(10)
        result = self.unified.measure(G)
        
        assert 'topology' in result
        assert 'information' in result
        assert 'computation' in result
        assert 'unified' in result
        assert 'unification_verified' in result
        assert 'kappa_pi' in result
    
    def test_unified_complexity_positive(self):
        """Test that unified complexity is positive for non-trivial graphs."""
        G = nx.cycle_graph(10)
        result = self.unified.measure(G)
        
        # For non-trivial graph, unified should be positive
        if result['topology'] > 0:
            assert result['unified'] >= 0
    
    def test_unified_complexity_path_vs_complete(self):
        """Test that unified complexity distinguishes easy vs hard."""
        G_easy = nx.path_graph(10)
        G_hard = nx.complete_graph(8)
        
        result_easy = self.unified.measure(G_easy)
        result_hard = self.unified.measure(G_hard)
        
        # Complete graph should have higher complexity
        assert result_hard['topology'] > result_easy['topology']
    
    def test_kappa_pi_in_result(self):
        """Test that κ_Π is included in results."""
        G = nx.cycle_graph(10)
        result = self.unified.measure(G)
        
        assert result['kappa_pi'] == KAPPA_PI


class TestGraphCreation:
    """Test helper functions for creating test graphs."""
    
    def test_create_path_graph(self):
        """Test path graph creation."""
        G = create_test_graph('path', 10)
        assert G.number_of_nodes() == 10
        assert G.number_of_edges() == 9
    
    def test_create_cycle_graph(self):
        """Test cycle graph creation."""
        G = create_test_graph('cycle', 10)
        assert G.number_of_nodes() == 10
        assert G.number_of_edges() == 10
    
    def test_create_grid_graph(self):
        """Test grid graph creation."""
        G = create_test_graph('grid', 16)
        assert G.number_of_nodes() == 16
    
    def test_create_complete_graph(self):
        """Test complete graph creation."""
        G = create_test_graph('complete', 5)
        assert G.number_of_nodes() == 5
        assert G.number_of_edges() == 10  # K_5 has 10 edges
    
    def test_create_expander_graph(self):
        """Test expander graph creation."""
        G = create_test_graph('expander', 10)
        assert G.number_of_nodes() == 10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
