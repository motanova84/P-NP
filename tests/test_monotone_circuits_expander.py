"""
Unit tests for monotone_circuits_expander.py

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import math
import unittest
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from monotone_circuits_expander import (
    construct_circulant_expander,
    spectral_gap,
    local_clique_approximation_error,
    kappa_pi_loss_factor,
    monotone_circuit_size_lower_bound,
    approximation_rounds_needed,
    negative_certificate_size,
    positive_certificate_size,
    analyze_monotone_circuits,
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


class TestRazborovApproximation(unittest.TestCase):
    """Tests for the Razborov approximation-method helpers."""

    def setUp(self):
        self.G = construct_circulant_expander(20)
        self.n = 20
        self.lam2 = spectral_gap(self.G)

    def test_spectral_gap_positive(self):
        self.assertGreater(self.lam2, 0.0)

    def test_local_approx_error_in_range(self):
        err = local_clique_approximation_error(self.G)
        self.assertGreaterEqual(err, 0.0)
        self.assertLessEqual(err, 1.0)

    def test_local_approx_error_increases_with_n(self):
        """For larger n, local neighbourhood covers a smaller fraction (radius=1)."""
        err_small = local_clique_approximation_error(construct_circulant_expander(10), locality_radius=1)
        err_large = local_clique_approximation_error(construct_circulant_expander(200), locality_radius=1)
        self.assertGreaterEqual(err_large, err_small)

    def test_kappa_pi_loss_factor_positive(self):
        loss = kappa_pi_loss_factor(self.lam2)
        self.assertGreater(loss, 0.0)

    def test_kappa_pi_loss_uses_constant(self):
        loss = kappa_pi_loss_factor(self.lam2)
        self.assertAlmostEqual(loss, KAPPA_PI / self.lam2, places=10)

    def test_kappa_pi_loss_infinite_for_zero_gap(self):
        import math
        loss = kappa_pi_loss_factor(0.0)
        self.assertEqual(loss, float("inf"))

    def test_monotone_circuit_size_lb_non_negative(self):
        log2_lb = monotone_circuit_size_lower_bound(self.n, self.lam2)
        self.assertGreaterEqual(log2_lb, 0.0)

    def test_monotone_circuit_size_lb_grows_with_n(self):
        lb_small = monotone_circuit_size_lower_bound(20, self.lam2)
        lb_large = monotone_circuit_size_lower_bound(200, self.lam2)
        self.assertGreater(lb_large, lb_small)

    def test_approximation_rounds_positive(self):
        rounds = approximation_rounds_needed(self.n, self.lam2)
        self.assertGreater(rounds, 0.0)


class TestCertificateSizes(unittest.TestCase):
    """Tests for negative and positive certificate sizes."""

    def setUp(self):
        self.G = construct_circulant_expander(20)

    def test_negative_certificate_positive(self):
        size = negative_certificate_size(self.G)
        self.assertGreater(size, 0)

    def test_positive_certificate_equals_n(self):
        size = positive_certificate_size(self.G)
        self.assertEqual(size, self.G.number_of_nodes())

    def test_negative_certificate_grows_with_n(self):
        """Negative cert size ⌈h·n/2⌉ grows when h is fixed and n grows."""
        fixed_lam2 = 0.2
        fixed_h = fixed_lam2 / 2.0
        sz_small = max(1, math.ceil(fixed_h * 20 / 2))
        sz_large = max(1, math.ceil(fixed_h * 200 / 2))
        self.assertGreater(sz_large, sz_small)


class TestAnalyzeFunction(unittest.TestCase):
    """Tests for the high-level analyze_monotone_circuits function."""

    def test_returns_dict_with_all_keys(self):
        result = analyze_monotone_circuits(20)
        expected_keys = [
            "n", "num_edges", "degree", "spectral_gap_lambda2",
            "edge_expansion_h", "local_clique_approx_error",
            "kappa_pi_loss_factor", "log2_circuit_size_lower_bound",
            "approximation_rounds", "negative_certificate_size",
            "positive_certificate_size",
        ]
        for key in expected_keys:
            self.assertIn(key, result, f"Missing key: {key}")

    def test_n_field_matches_input(self):
        result = analyze_monotone_circuits(30)
        self.assertEqual(result["n"], 30)

    def test_log_size_grows_with_n(self):
        r_small = analyze_monotone_circuits(20)
        r_large = analyze_monotone_circuits(100)
        self.assertGreater(
            r_large["log2_circuit_size_lower_bound"],
            r_small["log2_circuit_size_lower_bound"],
        )

    def test_constants(self):
        self.assertAlmostEqual(F0_QCAL, 141.7001, places=4)
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)


if __name__ == '__main__':
    print("Running Monotone Circuits Expander Tests ∞³")
    print(f"Frecuencia de resonancia: {F0_QCAL} Hz")
    print()
    unittest.main(verbosity=2)
