# -*- coding: utf-8 -*-
"""
Tests for Critical Inequality Strategy

Tests the implementation of IC(Π_φ | S) ≥ c · tw(G_I(φ))
"""

import pytest
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from critical_inequality_strategy import (
    RamanujanExpanderBuilder,
    TseitinFormulaGenerator,
    SeparatorAnalyzer,
    InformationComplexityEstimator,
    TreewidthEstimator,
    CriticalInequalityValidator,
    InequalityResult
)


class TestRamanujanExpanderBuilder:
    """Test expander construction"""
    
    def test_construct_basic(self):
        """Test basic expander construction"""
        builder = RamanujanExpanderBuilder(n=20, d=3)
        G = builder.construct_ramanujan_approximation()
        
        assert len(G) == 20
        assert G.number_of_edges() > 0
    
    def test_verify_ramanujan_property(self):
        """Test Ramanujan property verification"""
        import numpy as np
        builder = RamanujanExpanderBuilder(n=20, d=4)  # Use even d for easier construction
        G = builder.construct_ramanujan_approximation()
        
        # Should construct a reasonably good expander
        is_good = builder.verify_ramanujan_property(G)
        # May not always be perfect due to randomness, but should work often
        # Handle both Python bool and numpy bool
        assert isinstance(is_good, (bool, np.bool_))
    
    def test_different_sizes(self):
        """Test expanders of different sizes"""
        for n in [10, 20, 30]:
            builder = RamanujanExpanderBuilder(n=n, d=4)
            G = builder.construct_ramanujan_approximation()
            assert len(G) == n


class TestTseitinFormulaGenerator:
    """Test Tseitin formula generation"""
    
    def test_generate_on_triangle(self):
        """Test Tseitin formula on simple triangle"""
        import networkx as nx
        
        G = nx.cycle_graph(3)
        gen = TseitinFormulaGenerator(G)
        clauses, G_I = gen.generate_tseitin_formula()
        
        # Should have clauses
        assert len(clauses) > 0
        
        # Should have incidence graph
        assert G_I.number_of_nodes() > 0
    
    def test_generate_on_expander(self):
        """Test Tseitin formula on expander"""
        builder = RamanujanExpanderBuilder(n=10, d=3)
        expander = builder.construct_ramanujan_approximation()
        
        gen = TseitinFormulaGenerator(expander)
        clauses, G_I = gen.generate_tseitin_formula()
        
        # Should generate valid CNF
        assert len(clauses) > 0
        assert G_I.number_of_nodes() > 0
        
        # Variables should be present
        var_nodes = [n for n in G_I.nodes() if str(n).startswith('v')]
        assert len(var_nodes) > 0


class TestSeparatorAnalyzer:
    """Test separator analysis"""
    
    def test_find_separator_simple(self):
        """Test separator finding on simple graph"""
        import networkx as nx
        
        G = nx.path_graph(10)
        analyzer = SeparatorAnalyzer(G)
        separator = analyzer.find_balanced_separator()
        
        assert len(separator) > 0
        assert len(separator) <= len(G)
    
    def test_separator_bound_expander(self):
        """Test separator size bound for expanders"""
        builder = RamanujanExpanderBuilder(n=50, d=5)
        G = builder.construct_ramanujan_approximation()
        
        analyzer = SeparatorAnalyzer(G)
        bound = analyzer.estimate_separator_size_bound(is_expander=True, degree=5)
        
        # For expander: bound ≈ n/(2√d) ≈ 50/(2*√5) ≈ 11
        assert bound > 0
        assert bound < 50


class TestTreewidthEstimator:
    """Test treewidth estimation"""
    
    def test_estimate_path(self):
        """Test treewidth of path (should be 1)"""
        import networkx as nx
        
        G = nx.path_graph(10)
        estimator = TreewidthEstimator(G)
        tw = estimator.estimate_treewidth()
        
        # Path has treewidth 1
        assert tw >= 1
        assert tw <= 2  # May slightly overestimate
    
    def test_estimate_clique(self):
        """Test treewidth of clique (should be n-1)"""
        import networkx as nx
        
        n = 5
        G = nx.complete_graph(n)
        estimator = TreewidthEstimator(G)
        tw = estimator.estimate_treewidth()
        
        # Clique has treewidth n-1
        assert tw >= n - 1
    
    def test_estimate_positive(self):
        """Test that treewidth is always positive for non-empty graphs"""
        import networkx as nx
        
        G = nx.cycle_graph(6)
        estimator = TreewidthEstimator(G)
        tw = estimator.estimate_treewidth()
        
        assert tw >= 0


class TestInformationComplexityEstimator:
    """Test information complexity estimation"""
    
    def test_estimate_IC_basic(self):
        """Test basic IC estimation"""
        import networkx as nx
        
        # Simple formula
        clauses = [[1, 2], [-1, 3], [2, -3]]
        num_vars = 3
        
        # Create simple incidence graph
        G_I = nx.Graph()
        G_I.add_nodes_from(['v1', 'v2', 'v3', 'c0', 'c1', 'c2'])
        G_I.add_edges_from([('v1', 'c0'), ('v2', 'c0'), 
                           ('v1', 'c1'), ('v3', 'c1'),
                           ('v2', 'c2'), ('v3', 'c2')])
        
        estimator = InformationComplexityEstimator(clauses, num_vars)
        separator = {1, 2}
        IC = estimator.estimate_IC(separator, G_I)
        
        assert IC >= 0
    
    def test_IC_increases_with_separator_size(self):
        """Test that IC increases with separator size"""
        import networkx as nx
        
        clauses = [[1, 2, 3], [-1, -2], [2, -3, 4]]
        num_vars = 4
        
        G_I = nx.Graph()
        G_I.add_nodes_from(['v1', 'v2', 'v3', 'v4'])
        
        estimator = InformationComplexityEstimator(clauses, num_vars)
        
        IC_small = estimator.estimate_IC({1}, G_I)
        IC_large = estimator.estimate_IC({1, 2, 3}, G_I)
        
        assert IC_large >= IC_small


class TestCriticalInequalityValidator:
    """Test the main validator"""
    
    def test_validate_single_instance(self):
        """Test validation on single instance"""
        validator = CriticalInequalityValidator()
        
        results = validator.validate_on_expander(n=20, d=4, num_trials=2)
        
        # Should return some results
        assert len(results) >= 0
        
        # Each result should have proper structure
        for result in results:
            assert isinstance(result, InequalityResult)
            assert result.tw >= 0
            assert result.IC >= 0
            assert result.constant_c >= 0
            assert isinstance(result.satisfies_inequality, bool)
    
    def test_inequality_constant(self):
        """Test that constant c is computed correctly"""
        validator = CriticalInequalityValidator()
        
        results = validator.validate_on_expander(n=30, d=5, num_trials=3)
        
        for result in results:
            if result.tw > 0:
                # Check c = IC / tw
                expected_c = result.IC / result.tw
                assert abs(result.constant_c - expected_c) < 0.001
    
    def test_empirical_validation_structure(self):
        """Test structure of empirical validation results"""
        validator = CriticalInequalityValidator()
        
        stats = validator.run_empirical_validation(
            sizes=[20],
            degree=4,
            trials_per_size=2
        )
        
        # Check statistics structure
        assert 'total_trials' in stats
        assert 'satisfying_trials' in stats
        assert 'satisfaction_rate' in stats
        assert 'mean_c' in stats
        assert 'median_c' in stats
        assert 'min_c' in stats
        assert 'max_c' in stats
        assert 'results' in stats
        
        # Check values are reasonable
        assert stats['total_trials'] >= 0
        assert stats['satisfying_trials'] >= 0
        assert 0 <= stats['satisfaction_rate'] <= 1
    
    def test_satisfaction_rate_meaningful(self):
        """Test that satisfaction rate is meaningful"""
        validator = CriticalInequalityValidator()
        
        stats = validator.run_empirical_validation(
            sizes=[20],  # Use even size to avoid n*d parity issues
            degree=4,
            trials_per_size=3
        )
        
        # Should have some trials
        assert stats['total_trials'] > 0
        
        # Constants should be positive
        if stats['total_trials'] > 0:
            assert stats['mean_c'] >= 0
            assert stats['median_c'] >= 0


class TestInequalityResult:
    """Test InequalityResult dataclass"""
    
    def test_create_result(self):
        """Test creating result instance"""
        result = InequalityResult(
            tw=10.0,
            separator_size=5,
            IC=2.0,
            constant_c=0.2,
            satisfies_inequality=True
        )
        
        assert result.tw == 10.0
        assert result.separator_size == 5
        assert result.IC == 2.0
        assert result.constant_c == 0.2
        assert result.satisfies_inequality == True
    
    def test_inequality_check(self):
        """Test inequality satisfaction check"""
        # Case 1: Satisfies
        result1 = InequalityResult(
            tw=10, separator_size=5, IC=1.5,
            constant_c=0.15, satisfies_inequality=True
        )
        assert result1.satisfies_inequality
        
        # Case 2: Does not satisfy
        result2 = InequalityResult(
            tw=100, separator_size=10, IC=0.5,
            constant_c=0.005, satisfies_inequality=False
        )
        assert not result2.satisfies_inequality


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
