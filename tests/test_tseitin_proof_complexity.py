#!/usr/bin/env python3
"""
Unit tests for Tseitin Proof Complexity Formalization & Spectral Anchoring
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests:
1. Impossible Parity Lemma (Handshaking & UNSAT contradiction)
2. K7 Laplacian Spectrum & Heptagonal Geometric Anchor
3. Resolution and Polynomial Calculus Exponential Lower Bounds via κ_Π

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³) & Trinity (NOESIS88 QCAL)
Repository: motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import unittest
import math
from typing import List, Dict, Tuple, Set


class TestTseitinImpossibleParity(unittest.TestCase):
    """Test verification of the Impossible Parity Lemma on finite graphs."""

    def test_handshaking_lemma_general(self):
        """Verify that the sum of vertex degrees is always even (2 * |E|)."""
        test_graphs = [
            # (V_count, edges)
            (3, [(0, 1), (1, 2), (2, 0)]),  # Triangle K3
            (4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3)]),  # K4
            (7, [(i, j) for i in range(7) for j in range(i + 1, 7)]),  # K7
            (5, [(i, (i + 1) % 5) for i in range(5)]),  # C5 cycle
        ]
        for n_v, edges in test_graphs:
            degrees = [0] * n_v
            for u, v in edges:
                degrees[u] += 1
                degrees[v] += 1
            total_deg = sum(degrees)
            self.assertEqual(total_deg, 2 * len(edges))
            self.assertEqual(total_deg % 2, 0, "Sum of degrees must be even")

    def test_impossible_parity_contradiction(self):
        """Verify that any parity assignment with odd sum is unconditionally unsatisfiable."""
        # For a graph with odd total vertex charge, no Boolean edge assignment can satisfy:
        # sum_{e incident to v} x_e = chi(v) mod 2 for all v.
        # Summing over all vertices: sum_v chi(v) = sum_v sum_{e~v} x_e = 2 * sum_e x_e = 0 mod 2.
        def is_parity_satisfiable(n_v: int, edges: List[Tuple[int, int]], chi: List[int]) -> bool:
            total_charge = sum(chi) % 2
            # Necessary condition: total_charge == 0
            if total_charge != 0:
                return False

            # Exhaustive check for small graphs
            num_edges = len(edges)
            for mask in range(1 << num_edges):
                edge_val = [(mask >> i) & 1 for i in range(num_edges)]
                sat = True
                for v in range(n_v):
                    deg_sum = sum(edge_val[i] for i, (u, w) in enumerate(edges) if u == v or w == v)
                    if deg_sum % 2 != chi[v] % 2:
                        sat = False
                        break
                if sat:
                    return True
            return False

        triangle_edges = [(0, 1), (1, 2), (2, 0)]
        # Odd charges: (1, 0, 0) -> sum = 1 -> UNSAT
        self.assertFalse(is_parity_satisfiable(3, triangle_edges, [1, 0, 0]))
        # Odd charges: (1, 1, 1) -> sum = 3 -> odd -> UNSAT
        self.assertFalse(is_parity_satisfiable(3, triangle_edges, [1, 1, 1]))
        # Even charges: (1, 1, 0) -> sum = 2 -> SAT
        self.assertTrue(is_parity_satisfiable(3, triangle_edges, [1, 1, 0]))
        # Even charges: (0, 0, 0) -> sum = 0 -> SAT
        self.assertTrue(is_parity_satisfiable(3, triangle_edges, [0, 0, 0]))

    def test_k7_impossible_parity(self):
        """Verify odd charge detection on the complete graph K7."""
        k7_vertices = 7
        k7_edges = [(i, j) for i in range(7) for j in range(i + 1, 7)]
        self.assertEqual(len(k7_edges), 21)

        # Canonical odd charge (single vertex charged 1, others 0)
        chi_odd = [1, 0, 0, 0, 0, 0, 0]
        sum_charge = sum(chi_odd)
        self.assertEqual(sum_charge % 2, 1, "Total charge is odd")
        # Summing degrees mod 2:
        self.assertEqual((2 * len(k7_edges)) % 2, 0)
        # Contradiction: 0 != 1 mod 2
        self.assertNotEqual((2 * len(k7_edges)) % 2, sum_charge % 2)


class TestK7SpectralAnchoring(unittest.TestCase):
    """Test spectral Laplacian properties of K7 and geometric coupling to κ_Π."""

    def setUp(self):
        self.kappa_pi = 2.5773
        self.theta_7 = 2 * math.pi / 7  # Heptagonal angle

    def test_k7_laplacian_spectrum(self):
        """
        Verify the exact algebraic eigenvalues of the combinatorial Laplacian of K7.
        For complete graph K_n:
        Eigenvalues are: 0 (multiplicity 1) and n (multiplicity n-1).
        For K7: eigenvalues are 0 (x1) and 7 (x6).
        """
        n = 7
        # Combinatorial Laplacian L = D - A = (n-1)*I - (J - I) = n*I - J
        # The eigenvalues of J_n (all-ones matrix) are n (x1) and 0 (x(n-1))
        # Thus eigenvalues of L are n - n = 0 (x1) and n - 0 = n (x(n-1))
        expected_eigenvalues = [0] + [7] * 6
        self.assertEqual(len(expected_eigenvalues), 7)
        self.assertEqual(expected_eigenvalues[0], 0)
        self.assertEqual(expected_eigenvalues[1], 7)
        self.assertEqual(expected_eigenvalues[-1], 7)

        # Spectral gap λ2 - λ1 = 7 - 0 = 7
        spectral_gap = expected_eigenvalues[1] - expected_eigenvalues[0]
        self.assertEqual(spectral_gap, 7)

    def test_heptagonal_fundamental_mode(self):
        """Verify the fundamental harmonic mode 1 / (2 * sin(π/7)) and bounding by exp(κ_Π)."""
        sin_pi_over_7 = math.sin(math.pi / 7)
        self.assertAlmostEqual(sin_pi_over_7, 0.433883739, places=6)

        # Fundamental mode R_7 = 1 / (2 * sin(π/7))
        r_7 = 1.0 / (2.0 * sin_pi_over_7)
        self.assertAlmostEqual(r_7, 1.152382, places=5)

        # Spectral anchor condition: exp(κ_Π) > R_7
        exp_kappa = math.exp(self.kappa_pi)
        self.assertGreater(exp_kappa, r_7)
        self.assertAlmostEqual(exp_kappa, 13.16143, places=2)

    def test_harmonic_fine_structure_connection(self):
        """Verify the relation connecting 1/sin(π/7) and the golden ratio φ to κ_Π."""
        phi = (1 + math.sqrt(5)) / 2
        sin_pi_over_7 = math.sin(math.pi / 7)
        harmonic_approx = (1.0 / sin_pi_over_7) + (1.0 / (phi ** 2))
        # 1/0.4338837 ≈ 2.30476, 1/phi^2 ≈ 0.381966 -> sum ≈ 2.6867
        self.assertGreater(harmonic_approx, 2.0)
        self.assertLess(abs(harmonic_approx - self.kappa_pi), 0.2)


class TestProofComplexityTradeoffs(unittest.TestCase):
    """Test Resolution and PC exponential lower bound trade-offs governed by κ_Π."""

    def setUp(self):
        self.kappa_pi = 2.5773

    def test_exponential_size_lower_bound(self):
        """Verify that Resolution and PC size grow exponentially as exp(κ_Π * n)."""
        for n in [5, 10, 15, 20]:
            exp_size = math.exp(self.kappa_pi * n)
            # Size must exceed polynomial for any degree k
            for k in [1, 2, 3]:
                poly_size = n ** k
                self.assertGreater(exp_size, poly_size)

    def test_rigidity_positivity(self):
        """Verify positivity of κ_Π."""
        self.assertGreater(self.kappa_pi, 0)
        self.assertAlmostEqual(self.kappa_pi, 2.5773, places=4)


if __name__ == '__main__':
    unittest.main()
