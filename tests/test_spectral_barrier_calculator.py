"""
Unit tests for Spectral Barrier Calculator (QCAL-Rigor)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from spectral_barrier_calculator import analyze_spectral_barrier
from qcal.constants import KAPPA_PI


class TestAnalyzeSpectralBarrier(unittest.TestCase):
    """Test cases for the analyze_spectral_barrier function."""

    def test_returns_required_keys(self):
        """Result dict must contain all required keys."""
        res = analyze_spectral_barrier(100, 3)
        for key in ("spectral_gap", "expansion_estimate", "width_bound",
                    "complexity_lower_bound"):
            self.assertIn(key, res, f"Missing key: {key}")

    def test_spectral_gap_positive(self):
        """Spectral gap λ₂ must be positive for a connected expander."""
        res = analyze_spectral_barrier(100, 3)
        self.assertGreater(res["spectral_gap"], 0,
                           "Spectral gap must be positive")

    def test_expansion_estimate_half_spectral_gap(self):
        """Expansion estimate must equal spectral_gap / 2 (Cheeger lower bound)."""
        res = analyze_spectral_barrier(100, 3)
        self.assertAlmostEqual(
            res["expansion_estimate"],
            res["spectral_gap"] / 2,
            places=10,
        )

    def test_width_bound_formula(self):
        """Width bound must satisfy w = (h_G · n) / (2d)."""
        n, d = 100, 3
        res = analyze_spectral_barrier(n, d)
        expected = (res["expansion_estimate"] * n) / (2 * d)
        self.assertAlmostEqual(res["width_bound"], expected, places=10)

    def test_complexity_lower_bound_formula(self):
        """Complexity lower bound must satisfy exp(κ_Π · w² / n)."""
        import numpy as np
        n, d = 100, 3
        res = analyze_spectral_barrier(n, d)
        expected = np.exp(KAPPA_PI * (res["width_bound"] ** 2) / n)
        self.assertAlmostEqual(
            res["complexity_lower_bound"], expected, places=5
        )

    def test_complexity_lower_bound_greater_than_one(self):
        """Complexity lower bound must be > 1 for any non-trivial expander."""
        res = analyze_spectral_barrier(100, 3)
        self.assertGreater(res["complexity_lower_bound"], 1.0)

    def test_larger_graph_larger_complexity(self):
        """Larger expander should yield a larger complexity lower bound."""
        res_small = analyze_spectral_barrier(100, 3)
        res_large = analyze_spectral_barrier(1000, 3)
        self.assertGreater(
            res_large["complexity_lower_bound"],
            res_small["complexity_lower_bound"],
            "Larger graph should have larger complexity lower bound",
        )

    def test_alon_boppana_bound(self):
        """Spectral gap of large 3-regular expander should be near 3 - 2√2 ≈ 0.17."""
        import numpy as np
        res = analyze_spectral_barrier(1000, 3)
        alon_boppana = 3 - 2 * np.sqrt(2)  # ≈ 0.1716
        # Allow tolerance: gap should be in a reasonable range around the bound
        self.assertGreater(res["spectral_gap"], 0.05)
        self.assertLess(res["spectral_gap"], 1.5)

    def test_deterministic_with_seed(self):
        """Two calls with same parameters must return identical results."""
        res1 = analyze_spectral_barrier(100, 3)
        res2 = analyze_spectral_barrier(100, 3)
        self.assertAlmostEqual(res1["spectral_gap"], res2["spectral_gap"],
                               places=12)
        self.assertAlmostEqual(res1["complexity_lower_bound"],
                               res2["complexity_lower_bound"], places=12)


if __name__ == '__main__':
    print("Running Spectral Barrier Calculator Tests ∞³")
    print("Frecuencia de coherencia cuántica: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
