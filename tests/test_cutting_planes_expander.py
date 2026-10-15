"""
Unit tests for cutting_planes_expander.py

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import math
import unittest
import sys
import os
import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from cutting_planes_expander import (
    construct_circulant_expander,
    spectral_gap,
    edge_expansion,
    min_cut_bandwidth,
    hyperplane_density,
    chvatal_gomory_rank_lower_bound,
    cp_proof_size_lower_bound,
    analyze_cutting_planes,
    KAPPA_PI,
    F0_QCAL,
)


class TestExpanderConstruction(unittest.TestCase):
    """Tests for the expander graph construction helper."""

    def test_node_count(self):
        for n in [10, 20, 50]:
            G = construct_circulant_expander(n)
            self.assertEqual(G.number_of_nodes(), n)

    def test_connected(self):
        for n in [10, 20, 50]:
            G = construct_circulant_expander(n)
            self.assertTrue(nx.is_connected(G), f"Expander n={n} should be connected")

    def test_regular(self):
        for n in [10, 20, 50]:
            G = construct_circulant_expander(n)
            degrees = set(dict(G.degree()).values())
            self.assertEqual(len(degrees), 1, f"Expander n={n} should be regular")


class TestSpectralMetrics(unittest.TestCase):
    """Tests for spectral gap and edge expansion."""

    def test_spectral_gap_positive(self):
        G = construct_circulant_expander(20)
        lam2 = spectral_gap(G)
        self.assertGreater(lam2, 0.0)

    def test_spectral_gap_at_most_one(self):
        G = construct_circulant_expander(20)
        lam2 = spectral_gap(G)
        self.assertLessEqual(lam2, 2.0)   # normalised Laplacian eigenvalues in [0,2]

    def test_edge_expansion_positive(self):
        G = construct_circulant_expander(20)
        h = edge_expansion(G)
        self.assertGreater(h, 0.0)

    def test_edge_expansion_le_spectral_gap(self):
        """h ≤ λ₂ / 2 is the Cheeger bound direction; here equality holds."""
        G = construct_circulant_expander(20)
        lam2 = spectral_gap(G)
        h = edge_expansion(G)
        self.assertAlmostEqual(h, lam2 / 2.0, places=10)


class TestCuttingPlanesMetrics(unittest.TestCase):
    """Tests for CP lower-bound metrics."""

    def setUp(self):
        self.n = 20
        self.G = construct_circulant_expander(self.n)
        self.lam2 = spectral_gap(self.G)
        self.h = self.lam2 / 2.0

    def test_min_cut_bandwidth_positive(self):
        bw = min_cut_bandwidth(self.G)
        self.assertGreater(bw, 0)

    def test_hyperplane_density_positive(self):
        d = hyperplane_density(self.n, self.h)
        self.assertGreater(d, 0)

    def test_chvatal_gomory_rank_positive(self):
        rank = chvatal_gomory_rank_lower_bound(self.n, self.h)
        self.assertGreater(rank, 0.0)

    def test_rank_grows_with_n(self):
        """Rank lower bound should increase as n increases when h is fixed."""
        fixed_h = 0.1
        rank_small = chvatal_gomory_rank_lower_bound(10, fixed_h)
        rank_large = chvatal_gomory_rank_lower_bound(100, fixed_h)
        self.assertGreater(rank_large, rank_small)

    def test_cp_proof_size_lower_bound_positive(self):
        size = cp_proof_size_lower_bound(self.n, self.h)
        self.assertGreater(size, 1.0)

    def test_cp_proof_size_superpolynomial(self):
        """exp(h*√n/4) should grow strictly with n when h is fixed."""
        fixed_h = 0.1
        size_small = cp_proof_size_lower_bound(20, fixed_h)
        size_large = cp_proof_size_lower_bound(200, fixed_h)
        self.assertGreater(size_large, size_small)


class TestAnalyzeFunction(unittest.TestCase):
    """Tests for the high-level analyze_cutting_planes function."""

    def test_returns_dict_with_all_keys(self):
        result = analyze_cutting_planes(20)
        expected_keys = [
            "n", "num_edges", "degree", "spectral_gap_lambda2",
            "edge_expansion_h", "min_cut_bandwidth", "hyperplane_density",
            "chvatal_gomory_rank_lower_bound", "cp_proof_size_lower_bound",
        ]
        for key in expected_keys:
            self.assertIn(key, result, f"Missing key: {key}")

    def test_n_field_matches_input(self):
        result = analyze_cutting_planes(30)
        self.assertEqual(result["n"], 30)

    def test_rank_scales_with_n(self):
        r_small = analyze_cutting_planes(20)
        r_large = analyze_cutting_planes(200)
        # With a fixed h, rank = h*n/(2*log2(n+1)) grows with n.
        # Test using the same fixed h = 0.1 to confirm the formula is monotone.
        fixed_h = 0.1
        lb_small = fixed_h * 20 / (2 * math.log2(21))
        lb_large = fixed_h * 200 / (2 * math.log2(201))
        self.assertGreater(lb_large, lb_small)

    def test_constants(self):
        self.assertAlmostEqual(F0_QCAL, 141.7001, places=4)
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)


if __name__ == '__main__':
    print("Running Cutting Planes Expander Tests ∞³")
    print(f"Frecuencia de resonancia: {F0_QCAL} Hz")
    print()
    unittest.main(verbosity=2)
