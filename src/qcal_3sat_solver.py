#!/usr/bin/env python3
"""
QCAL 3-SAT Resonant Solver
==========================

Continuous resonant solver over a 2^n Hilbert space embedding for 3-SAT.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Sequence, Tuple

import numpy as np
from scipy.linalg import expm


Clause = Sequence[Tuple[int, bool]]


@dataclass(frozen=True)
class QCALConfig:
    """Solver configuration."""

    f0: float = 141.7001
    epsilon: float = 0.05
    dt: float = 0.1
    steps: int = 50
    phase_scale: float = 1e-4


class QCAL3SATSolver:
    """Resonant 3-SAT solver based on diagonal clause-penalty Hamiltonians."""

    def __init__(self, config: QCALConfig | None = None):
        self.config = config or QCALConfig()
        self.omega0 = 2 * np.pi * self.config.f0

    @staticmethod
    def _state_bits(state: int, n_vars: int) -> List[int]:
        return [(state >> idx) & 1 for idx in range(n_vars)]

    @staticmethod
    def _clause_unsatisfied(state: int, clause: Clause) -> bool:
        for var_idx, is_positive in clause:
            bit_val = (state >> var_idx) & 1
            literal_val = bit_val == 1 if is_positive else bit_val == 0
            if literal_val:
                return False
        return True

    def build_hamiltonian_diag(self, n_vars: int, clauses: Sequence[Clause]) -> np.ndarray:
        """Build diagonal energies as number of violated clauses per state."""
        dim = 2**n_vars
        h_diag = np.zeros(dim, dtype=float)
        for state in range(dim):
            violations = 0.0
            for clause in clauses:
                if self._clause_unsatisfied(state, clause):
                    violations += 1.0
            h_diag[state] = violations
        return h_diag

    @staticmethod
    def build_resonant_coupling(dim: int) -> np.ndarray:
        """Global coupling operator R = (1 - I)/sqrt(dim)."""
        return (np.ones((dim, dim)) - np.eye(dim)) / np.sqrt(dim)

    def solve(self, n_vars: int, clauses: Sequence[Clause]) -> Dict[str, Any]:
        """Run resonant evolution and project to best assignment."""
        dim = 2**n_vars
        h_diag = self.build_hamiltonian_diag(n_vars, clauses)
        h_i = np.diag(h_diag)
        r = self.build_resonant_coupling(dim)
        a_eps = h_i + self.config.epsilon * r

        psi = np.ones(dim, dtype=complex) / np.sqrt(dim)

        times: List[float] = []
        coherences: List[float] = []
        probabilities: List[np.ndarray] = []

        valid_mask = h_diag == 0

        for step in range(self.config.steps):
            t = step * self.config.dt
            phase = np.exp(1j * self.omega0 * step * self.config.phase_scale)
            u = expm(-a_eps * self.config.dt * phase)
            psi = u @ psi
            psi = psi / np.linalg.norm(psi)

            probs = np.abs(psi) ** 2
            coherence = float(np.sum(probs[valid_mask])) if np.any(valid_mask) else 0.0

            times.append(t)
            coherences.append(coherence)
            probabilities.append(probs.copy())

        best_idx = int(np.argmax(np.abs(psi) ** 2))
        best_assignment = self._state_bits(best_idx, n_vars)

        return {
            "n_vars": n_vars,
            "dim": dim,
            "clauses": len(clauses),
            "hamiltonian_diag": h_diag,
            "ground_states": np.where(valid_mask)[0],
            "ground_state_count": int(np.sum(valid_mask)),
            "ground_state_index": best_idx,
            "solution": best_assignment,
            "satisfies_all": bool(h_diag[best_idx] == 0),
            "coherence": float(coherences[-1]) if coherences else 0.0,
            "times": np.array(times),
            "coherence_history": np.array(coherences),
            "probability_history": np.array(probabilities),
            "a_eps": a_eps,
        }

    def spectrum_report(self, a_eps: np.ndarray, ground_state_count: int) -> Dict[str, Any]:
        """Compute sorted eigenvalues and effective excitation gap."""
        eigenvalues = np.sort(np.real_if_close(np.linalg.eigvals(a_eps)).astype(float))
        gap_idx = min(max(ground_state_count, 1), len(eigenvalues) - 1)
        effective_gap = float(eigenvalues[gap_idx] - eigenvalues[ground_state_count - 1]) if ground_state_count > 0 else 0.0
        return {
            "eigenvalues": eigenvalues,
            "effective_gap": effective_gap,
        }

    def sampled_evolution_table(
        self, result: Dict[str, Any], sample_times: Sequence[float]
    ) -> List[Dict[str, float]]:
        """Create a probability/coherence table sampled at requested times."""
        times = result["times"]
        probs = result["probability_history"]
        ground_states = result["ground_states"]

        rows: List[Dict[str, float]] = []
        for target_t in sample_times:
            idx = int(np.argmin(np.abs(times - target_t)))
            row_probs = probs[idx]
            row: Dict[str, float] = {"t": float(times[idx])}
            for state in ground_states:
                row[f"P({int(state)})"] = float(row_probs[state])
            coherence = float(np.sum(row_probs[ground_states])) if len(ground_states) > 0 else 0.0
            row["Psi"] = coherence
            row["P_rest"] = float(1.0 - coherence)
            rows.append(row)
        return rows


def certified_instance() -> Tuple[int, List[Clause]]:
    """Reference certified instance used in NOESIS 3-SAT reports."""
    clauses: List[Clause] = [
        [(0, True), (1, True), (2, False)],
        [(0, False), (1, False), (3, True)],
        [(1, True), (2, True), (3, False)],
        [(0, True), (2, True), (3, True)],
        [(0, False), (1, True), (3, False)],
        [(1, False), (2, False), (3, False)],
        [(0, True), (1, False), (2, True)],
        [(0, False), (2, False), (3, True)],
    ]
    return 4, clauses


if __name__ == "__main__":
    solver = QCAL3SATSolver()
    n_vars, clauses = certified_instance()
    result = solver.solve(n_vars, clauses)
    spectrum = solver.spectrum_report(result["a_eps"], result["ground_state_count"])
    table = solver.sampled_evolution_table(result, [0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5])

    print("🌊 NOESIS — QCAL 3-SAT SOLVER")
    print(f"Variables: {result['n_vars']} | Cláusulas: {result['clauses']} | dim: {result['dim']}")
    print(f"Ground states: {result['ground_states'].tolist()}")
    print(f"Projected assignment: {tuple(result['solution'])}")
    print(f"Satisfies all: {result['satisfies_all']}")
    print(f"Final coherence Ψ: {result['coherence']:.6f}")
    print(f"Effective gap Δ_eff: {spectrum['effective_gap']:.6f}")
    print("\nEvolución temporal:")
    for row in table:
        print(row)
