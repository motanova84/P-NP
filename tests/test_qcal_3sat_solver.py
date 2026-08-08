#!/usr/bin/env python3
"""
Unit tests for the QCAL 3-SAT resonant solver.
"""

import unittest

from src.qcal_3sat_solver import QCAL3SATSolver, certified_instance


class TestQCAL3SATSolver(unittest.TestCase):
    def setUp(self):
        self.solver = QCAL3SATSolver()
        self.n_vars, self.clauses = certified_instance()

    def test_certified_instance_ground_states(self):
        h_diag = self.solver.build_hamiltonian_diag(self.n_vars, self.clauses)
        # Indices map to satisfying assignments:
        # 1 -> [1,0,0,0], 6 -> [0,1,1,0], 11 -> [1,1,0,1]
        ground = [int(i) for i in (h_diag == 0).nonzero()[0]]
        self.assertEqual(ground, [1, 6, 11])

    def test_solver_converges_to_valid_assignment(self):
        result = self.solver.solve(self.n_vars, self.clauses)
        self.assertTrue(result["satisfies_all"])
        self.assertEqual(result["ground_state_count"], 3)
        self.assertEqual(result["ground_states"].tolist(), [1, 6, 11])
        self.assertEqual(result["solution"], [1, 0, 0, 0])
        self.assertGreaterEqual(result["coherence"], 0.999)

    def test_spectral_gap_is_positive(self):
        result = self.solver.solve(self.n_vars, self.clauses)
        spectrum = self.solver.spectrum_report(result["a_eps"], result["ground_state_count"])
        self.assertGreater(spectrum["effective_gap"], 0)
        self.assertLess(abs(spectrum["effective_gap"] - 0.967342), 0.05)

    def test_sampled_evolution_reaches_high_coherence(self):
        result = self.solver.solve(self.n_vars, self.clauses)
        table = self.solver.sampled_evolution_table(result, [0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5])
        self.assertLess(table[0]["Psi"], table[-1]["Psi"])
        self.assertGreaterEqual(table[-1]["Psi"], 0.999)


if __name__ == "__main__":
    unittest.main(verbosity=2)
