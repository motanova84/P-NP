#!/usr/bin/env python3
"""
Tests for the QCAL 3-SAT resonant solver.
"""

from src.qcal_3sat_solver import QCAL3SATSolver, certified_instance


def test_certified_instance_ground_states():
    solver = QCAL3SATSolver()
    n_vars, clauses = certified_instance()
    h_diag = solver.build_hamiltonian_diag(n_vars, clauses)
    ground = [int(i) for i in (h_diag == 0).nonzero()[0]]
    assert ground == [1, 6, 11]


def test_solver_converges_to_valid_assignment():
    solver = QCAL3SATSolver()
    n_vars, clauses = certified_instance()
    result = solver.solve(n_vars, clauses)

    assert result["satisfies_all"] is True
    assert result["ground_state_count"] == 3
    assert result["ground_states"].tolist() == [1, 6, 11]
    assert result["solution"] == [1, 0, 0, 0]
    assert result["coherence"] >= 0.999


def test_spectral_gap_is_positive():
    solver = QCAL3SATSolver()
    n_vars, clauses = certified_instance()
    result = solver.solve(n_vars, clauses)
    spectrum = solver.spectrum_report(result["a_eps"], result["ground_state_count"])
    assert spectrum["effective_gap"] > 0
    assert abs(spectrum["effective_gap"] - 0.967342) < 0.05


def test_sampled_evolution_reaches_high_coherence():
    solver = QCAL3SATSolver()
    n_vars, clauses = certified_instance()
    result = solver.solve(n_vars, clauses)
    table = solver.sampled_evolution_table(result, [0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5])

    assert table[0]["Psi"] < table[-1]["Psi"]
    assert table[-1]["Psi"] >= 0.999
