"""
Unit tests for graph-dependent spectral constant κ_Π

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import unittest
import sys
import os
import math

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.spectral_kappa import (
    kappa_pi_for_incidence_graph,
    validate_kappa_bound,
    create_tseitin_incidence_graph,
    information_complexity_lower_bound_spectral,
    estimate_spectral_properties
)


class TestSpectralKappa(unittest.TestCase):
    """Test cases for graph-dependent κ_Π calculations."""
    
    def test_universal_method(self):
        """Test that universal method returns 2.5773."""
        G = create_tseitin_incidence_graph(10)
        κ = kappa_pi_for_incidence_graph(G, method="universal")
        self.assertAlmostEqual(κ, 2.5773, places=4)
    
    def test_conservative_method_scaling(self):
        """Test that conservative method scales as O(1/(√n log n))."""
        sizes = [100, 200, 400]
        kappas = []
        
        for n in sizes:
            G = create_tseitin_incidence_graph(n)
            κ = kappa_pi_for_incidence_graph(G, method="conservative")
            kappas.append(κ)
        
        # κ should decrease as n increases
        self.assertGreater(kappas[0], kappas[1])
        self.assertGreater(kappas[1], kappas[2])
        
        # Check approximate scaling
        # κ(200) / κ(100) ≈ √(100*log(100)) / √(200*log(200))
        # Using total vertices: 5*n
        n1_total = 5 * 100
        n2_total = 5 * 200
        ratio_observed = kappas[1] / kappas[0]
        ratio_expected = math.sqrt(n1_total * math.log(n1_total)) / math.sqrt(n2_total * math.log(n2_total))
        # Allow 50% tolerance due to discretization
        self.assertGreater(ratio_observed, ratio_expected * 0.5)
        self.assertLess(ratio_observed, ratio_expected * 1.5)
    
    def test_spectral_equals_conservative(self):
        """Test that spectral method gives same result as conservative (current implementation)."""
        G = create_tseitin_incidence_graph(100)
        κ_spectral = kappa_pi_for_incidence_graph(G, method="spectral")
        κ_conservative = kappa_pi_for_incidence_graph(G, method="conservative")
        self.assertAlmostEqual(κ_spectral, κ_conservative, places=6)
    
    def test_validate_kappa_bound_structure(self):
        """Test that validate_kappa_bound returns expected structure."""
        G = create_tseitin_incidence_graph(50)
        results = validate_kappa_bound(G, verbose=False)
        
        # Check all expected keys are present
        expected_keys = [
            'n_vertices', 'κ_spectral', 'κ_conservative', 'κ_universal',
            'theoretical_bound', 'satisfies_bound', 'lambda_2', 'd_avg', 'spectral_gap'
        ]
        for key in expected_keys:
            self.assertIn(key, results)
        
        # Check that κ_universal is 2.5773
        self.assertAlmostEqual(results['κ_universal'], 2.5773, places=4)
        
        # Check that bound is satisfied
        self.assertTrue(results['satisfies_bound'])
    
    def test_incidence_graph_structure(self):
        """Test that Tseitin incidence graph has expected structure."""
        n = 10
        G = create_tseitin_incidence_graph(n)
        
        # Should have n clauses + 4n variables = 5n vertices
        self.assertEqual(len(G.nodes()), 5 * n)
        
        # Check bipartite structure
        nodes_with_bipartite = sum(1 for _, d in G.nodes(data=True) if 'bipartite' in d)
        self.assertEqual(nodes_with_bipartite, 5 * n)
        
        # Count nodes of each type
        clause_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 0]
        var_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
        self.assertEqual(len(clause_nodes), n)
        self.assertEqual(len(var_nodes), 4 * n)
    
    def test_information_complexity_bound(self):
        """Test information complexity lower bound calculation."""
        G = create_tseitin_incidence_graph(100)
        treewidth = 10  # Example treewidth
        
        # Using spectral method (which is conservative)
        ic_spectral = information_complexity_lower_bound_spectral(treewidth, G, method="spectral")
        
        # Using universal constant
        ic_universal = information_complexity_lower_bound_spectral(treewidth, G, method="universal")
        
        # Spectral should give much larger IC (because κ is much smaller)
        self.assertGreater(ic_spectral, ic_universal)
        
        # IC should be positive
        self.assertGreater(ic_spectral, 0)
        self.assertGreater(ic_universal, 0)
    
    def test_estimate_spectral_properties(self):
        """Test spectral properties estimation."""
        G = create_tseitin_incidence_graph(50)
        lambda_2, d_avg, gap = estimate_spectral_properties(G)
        
        # Average degree should be around 3.2 for Tseitin incidence graphs
        # (n*8 + 4n*2) / (5n) = 16/5 = 3.2
        self.assertAlmostEqual(d_avg, 3.2, delta=0.1)
        
        # lambda_2 should be a valid eigenvalue (between 0 and 2 for normalized Laplacian)
        # Allow small numerical errors
        self.assertGreaterEqual(lambda_2, -1e-10)
        self.assertLessEqual(lambda_2, 2)
        
        # Gap should be between 0 and 1 (allowing numerical tolerance)
        self.assertGreaterEqual(gap, 0)
        self.assertLessEqual(gap, 1 + 1e-10)
    
    def test_small_graph_edge_cases(self):
        """Test edge cases with very small graphs."""
        G = create_tseitin_incidence_graph(1)
        
        # Should not crash
        κ = kappa_pi_for_incidence_graph(G, method="spectral")
        self.assertGreater(κ, 0)
        
        # Validation should work
        results = validate_kappa_bound(G, verbose=False)
        self.assertIsNotNone(results)


class TestTheoreticalBounds(unittest.TestCase):
    """Test theoretical bounds for κ_Π."""
    
    def test_kappa_decreases_with_n(self):
        """Test that κ_Π decreases as graph size increases."""
        prev_kappa = float('inf')
        
        for n in [10, 20, 50, 100, 200]:
            G = create_tseitin_incidence_graph(n)
            κ = kappa_pi_for_incidence_graph(G, method="spectral")
            
            # Each κ should be smaller than the previous
            self.assertLess(κ, prev_kappa)
            prev_kappa = κ
    
    def test_ic_increases_with_small_kappa(self):
        """Test that smaller κ_Π leads to larger IC bounds."""
        G = create_tseitin_incidence_graph(100)
        tw = 20
        
        # With universal κ (large)
        κ_large = 2.5773
        ic_with_large_kappa = tw / (2.0 * κ_large)
        
        # With graph-dependent κ (small)
        κ_small = kappa_pi_for_incidence_graph(G, method="spectral")
        ic_with_small_kappa = tw / (2.0 * κ_small)
        
        # Smaller κ should give larger IC
        self.assertLess(κ_small, κ_large)
        self.assertGreater(ic_with_small_kappa, ic_with_large_kappa)
    
    def test_theoretical_relationship(self):
        """Test the theoretical relationship: IC ≥ tw/(2κ_Π) ≥ Ω(n log n)."""
        n = 100
        G = create_tseitin_incidence_graph(n)
        
        # Assume tw ≤ O(√n)
        tw = math.sqrt(5 * n)  # 5n vertices total
        
        # κ ≤ O(1/(√n log n))
        κ = kappa_pi_for_incidence_graph(G, method="spectral")
        
        # Then IC ≥ tw/(2κ) should be Ω(n log n)
        ic = tw / (2.0 * κ)
        
        # Check that IC ≥ c * n * log(n) for some constant c
        n_vertices = 5 * n
        expected_lower = n_vertices * math.log(n_vertices) / 100  # Very conservative c
        
        self.assertGreater(ic, expected_lower)


if __name__ == '__main__':
    print("Running Graph-Dependent κ_Π Tests ∞³")
    print("Resonance frequency: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
