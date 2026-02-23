"""
Unit tests for branching_programs_expander.py

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import math
import unittest
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from branching_programs_expander import (
    construct_circulant_expander,
    spectral_gap,
    balanced_cut,
    information_flow_lower_bound,
    bp_width_lower_bound,
    bp_width_exponent,
    bp_length_lower_bound,
    bp_total_size_lower_bound,
    analyze_branching_programs,
    F0_QCAL,
    KAPPA_PI,
)


class TestExpanderConstruction(unittest.TestCase):
    """Tests for the shared expander construction helper."""

    def test_node_count(self):
        for n in [10, 20, 50]:
            G = construct_circulant_expander(n)
            self.assertEqual(G.number_of_nodes(), n)

    def test_regular(self):
        for n in [10, 20, 50]:
            G = construct_circulant_expander(n)
            degrees = set(dict(G.degree()).values())
            self.assertEqual(len(degrees), 1)


class TestCommunicationComplexity(unittest.TestCase):
    """Tests for the communication complexity / balanced cut helpers."""

    def setUp(self):
        self.G = construct_circulant_expander(20)

    def test_balanced_cut_non_empty_sides(self):
        left, right, crossing = balanced_cut(self.G)
        self.assertGreater(len(left), 0)
        self.assertGreater(len(right), 0)

    def test_balanced_cut_covers_all_nodes(self):
        left, right, crossing = balanced_cut(self.G)
        n = self.G.number_of_nodes()
        self.assertEqual(len(left) + len(right), n)

    def test_crossing_edges_positive(self):
        _, _, crossing = balanced_cut(self.G)
        self.assertGreater(crossing, 0)

    def test_information_flow_positive(self):
        flow = information_flow_lower_bound(self.G)
        self.assertGreater(flow, 0)


class TestBPMetrics(unittest.TestCase):
    """Tests for Branching Program width and size lower bounds."""

    def setUp(self):
        self.n = 20
        self.G = construct_circulant_expander(self.n)

    def test_width_lower_bound_positive(self):
        w = bp_width_lower_bound(self.G)
        self.assertGreater(w, 0)

    def test_width_exponent_positive(self):
        exp = bp_width_exponent(self.G)
        self.assertGreater(exp, 0.0)

    def test_length_lower_bound_positive(self):
        lb = bp_length_lower_bound(self.n)
        self.assertGreater(lb, 0.0)

    def test_length_grows_with_n(self):
        lb_small = bp_length_lower_bound(10)
        lb_large = bp_length_lower_bound(100)
        self.assertGreater(lb_large, lb_small)

    def test_total_size_lower_bound_positive(self):
        size = bp_total_size_lower_bound(self.G)
        self.assertGreater(size, 1.0)

    def test_total_size_superpolynomial(self):
        """Total BP size should grow strictly with n."""
        G_small = construct_circulant_expander(20)
        G_large = construct_circulant_expander(100)
        size_small = bp_total_size_lower_bound(G_small)
        size_large = bp_total_size_lower_bound(G_large)
        self.assertGreater(size_large, size_small)

    def test_width_exponent_grows_with_n(self):
        G_small = construct_circulant_expander(20)
        G_large = construct_circulant_expander(100)
        exp_small = bp_width_exponent(G_small)
        exp_large = bp_width_exponent(G_large)
        self.assertGreater(exp_large, exp_small)


class TestAnalyzeFunction(unittest.TestCase):
    """Tests for the high-level analyze_branching_programs function."""

    def test_returns_dict_with_all_keys(self):
        result = analyze_branching_programs(20)
        expected_keys = [
            "n", "num_edges", "degree", "spectral_gap_lambda2",
            "edge_expansion_h", "balanced_cut_crossing",
            "width_exponent", "width_lower_bound_log2",
            "length_lower_bound", "log2_total_size_lower_bound",
        ]
        for key in expected_keys:
            self.assertIn(key, result, f"Missing key: {key}")

    def test_n_field_matches_input(self):
        result = analyze_branching_programs(30)
        self.assertEqual(result["n"], 30)

    def test_log_size_grows_with_n(self):
        r_small = analyze_branching_programs(20)
        r_large = analyze_branching_programs(100)
        self.assertGreater(
            r_large["log2_total_size_lower_bound"],
            r_small["log2_total_size_lower_bound"],
        )

    def test_constants(self):
        self.assertAlmostEqual(F0_QCAL, 141.7001, places=4)
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)


if __name__ == '__main__':
    print("Running Branching Programs Expander Tests ∞³")
    print(f"Frecuencia de resonancia: {F0_QCAL} Hz")
    print()
    unittest.main(verbosity=2)
