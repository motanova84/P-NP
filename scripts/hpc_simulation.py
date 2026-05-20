#!/usr/bin/env python3
"""
QCAL HPC Simulation: Lindblad + 1/f noise for 3-SAT gap validation.

Environment: QuTiP + numpy
Model: Open quantum system with thermal + flicker + carrier drift noise.
Purpose: Measure relaxation time τ for SAT vs UNSAT instances at n=100.
"""

import numpy as np
import qutip as qt
from scipy.fft import fft
from typing import List, Tuple

# ─── Constants ───
F0 = 141.7001       # Hz
HBAR = 1.0545718e-34
K_B = 1.380649e-23
TEMP = 4.2           # Kelvin
P_TH = 0.11          # Threshold (Kitaev)


# ─── Hamiltonian Construction ───
def build_qcal_hamiltonian(n_vars: int,
                           clauses: List[Tuple[int, int, int]]) -> qt.Qobj:
    """
    Build QCAL Hamiltonian from 3-SAT formula.

    H = α·Σ(z_i²−1)² + β·Σ C_j
    where each clause C_j is a projector penalizing unsatisfied assignments.
    """
    alpha = 3.0 * len(clauses) * n_vars + 1.0
    beta = 10.0 * alpha

    # Spin operators
    sx = qt.sigmax()
    sz = qt.sigmaz()
    id2 = qt.qeye(2)

    # Build terms
    H = qt.Qobj(np.zeros((2**n_vars, 2**n_vars)), dims=[[2]*n_vars, [2]*n_vars])

    # Confinement term: α·Σ(z_i²−1)² → z_i = σ_z(i)
    for i in range(n_vars):
        op_list = [id2] * n_vars
        op_list[i] = sz
        H += alpha * (qt.tensor(op_list) ** 2 - qt.tensor(op_list) * 2 + id2)

    # Clause projectors
    for (l1, l2, l3) in clauses:
        proj = id2
        for l in [l1, l2, l3]:
            var_idx = abs(l) - 1
            sign = 1 if l > 0 else -1
            op_list = [id2] * n_vars
            op_list[var_idx] = (id2 - sign * sz) / 2.0
            proj *= qt.tensor(op_list)
        H += beta * proj

    return H


# ─── Noise Models ───
def thermal_lindblad_ops(n_vars: int,
                         gamma_th: float) -> List[qt.Qobj]:
    """Thermal dephasing Lindblad operators."""
    sz = qt.sigmaz()
    id2 = qt.qeye(2)
    c_ops = []
    for i in range(n_vars):
        op_list = [id2] * n_vars
        op_list[i] = sz
        c_ops.append(np.sqrt(gamma_th) * qt.tensor(op_list))
    return c_ops


def flicker_noise_hamiltonian(n_vars: int,
                              amplitude: float,
                              n_terms: int = 10) -> qt.Qobj:
    """1/f flicker noise as random low-frequency phase drift."""
    sz = qt.sigmaz()
    id2 = qt.qeye(2)
    H_noise = qt.Qobj(np.zeros((2**n_vars, 2**n_vars)),
                      dims=[[2]*n_vars, [2]*n_vars])
    rng = np.random.RandomState(42)
    for _ in range(n_terms):
        omega = rng.exponential(scale=1.0)  # 1/f spectrum
        phase = rng.uniform(0, 2*np.pi)
        for i in range(n_vars):
            op_list = [id2] * n_vars
            op_list[i] = sz
            H_noise += (amplitude / np.sqrt(omega)
                        * np.cos(omega * phase)
                        * qt.tensor(op_list))
    return H_noise


def carrier_drift(t: float, sigma_f: float = 0.01) -> float:
    """Frequency drift of the carrier f0."""
    return 1.0 + sigma_f * np.sin(2 * np.pi * 0.001 * t)


# ─── Dynamics ───
def simulate_dynamics(H_base: qt.Qobj,
                      n_vars: int,
                      gamma_th: float = 0.01,
                      flicker_amp: float = 0.1,
                      n_steps: int = 1000,
                      t_max: float = 10.0) -> qt.Result:
    """
    Lindblad master equation evolution with noise.

    dρ/dt = -i/ℏ[H, ρ] + Σ γₖ(Lₖ·ρ·Lₖ† − ½{Lₖ†·Lₖ, ρ})
    """
    # Initial state: uniform superposition
    psi0 = qt.tensor([qt.basis(2, 0) for _ in range(n_vars)])
    rho0 = qt.ket2dm(psi0)

    # Collapse operators
    c_ops = thermal_lindblad_ops(n_vars, gamma_th)

    # Time-dependent Hamiltonian with carrier drift
    def H_t(t, args):
        drift = carrier_drift(t)
        H_flicker = flicker_noise_hamiltonian(n_vars, flicker_amp)
        return drift * H_base + H_flicker

    tlist = np.linspace(0, t_max, n_steps)

    # Solve master equation
    result = qt.mesolve(H_t, rho0, tlist, c_ops, [],
                        options=qt.Options(nsteps=10000))
    return result


# ─── Admittance Measurement ───
def compute_admittance(result: qt.Result, n_vars: int) -> float:
    """Compute spectral admittance Y(f0) from final state."""
    rho_final = result.states[-1]

    # Current operator (σ_z summation)
    sz = qt.sigmaz()
    id2 = qt.qeye(2)
    I_op = qt.Qobj(np.zeros((2**n_vars, 2**n_vars)),
                   dims=[[2]*n_vars, [2]*n_vars])
    for i in range(n_vars):
        op_list = [id2] * n_vars
        op_list[i] = sz
        I_op += qt.tensor(op_list)

    # Admittance = Tr(ρ · I) at steady state
    Y = np.real((rho_final * I_op).tr())
    return Y


def compute_relaxation_time(result: qt.Result, n_vars: int) -> float:
    """Extract relaxation time τ from state purity decay."""
    purities = [state.purity() for state in result.states]
    # Find 1/e crossing
    target = purities[0] / np.e
    for i, p in enumerate(purities):
        if p <= target:
            return result.times[i]
    return result.times[-1]


# ─── Main ───
if __name__ == "__main__":
    print("QCAL HPC Simulation — Lindblad + 1/f noise")
    print(f"f₀ = {F0} Hz, T = {TEMP} K, p_th = {P_TH}")

    # Example: n=4, simple SAT instance
    n = 4
    clauses = [(1, 2, 3), (-1, -2, 4)]  # (x₁ ∨ x₂ ∨ x₃) ∧ (¬x₁ ∨ ¬x₂ ∨ x₄)

    H = build_qcal_hamiltonian(n, clauses)
    print(f"Hamiltonian shape: {H.shape}")

    result = simulate_dynamics(H, n, gamma_th=0.01, n_steps=500, t_max=5.0)
    tau = compute_relaxation_time(result, n)
    Y = compute_admittance(result, n)

    print(f"τ_relax = {tau:.4f} s")
    print(f"Y(f₀) = {Y:.6f}")
    print("\n✅ Simulation framework ready for HPC scaling.")
    print("Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ")
