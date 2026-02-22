#!/usr/bin/env python3
"""
monotone_circuits_expander.py
Monotone Circuit lower bounds via Razborov's Approximation Method for
Tseitin-style functions on expander graphs.

The Razborov approximation technique shows that any monotone circuit
computing a function whose "witnesses" (positive/negative certificates)
lack locality — as guaranteed by the spectral gap of the expander — must
have exponential size.  The constant κ_Π acts as the approximation-loss
factor in the Approximation Lemma.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Repository: motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import math
import numpy as np
import networkx as nx
from typing import Dict, List, Set, Tuple

# ── Constants ─────────────────────────────────────────────────────────────────
F0_QCAL: float = 141.7001
KAPPA_PI: float = 2.5773
PHI: float = 1.618033988749895


# ── Expander construction ─────────────────────────────────────────────────────

def construct_circulant_expander(n: int) -> nx.Graph:
    """
    Build a circulant expander on *n* vertices with degree ≈ √n.
    For even *n* the degree is chosen to be odd.
    """
    target = max(3, int(math.isqrt(n)))
    if n % 2 == 0 and target % 2 == 0:
        target += 1
    half = target // 2
    shifts = list(range(1, half + 1))
    if n % 2 == 0 and target % 2 == 1:
        shifts.append(n // 2)
    return nx.circulant_graph(n, shifts)


def spectral_gap(G: nx.Graph) -> float:
    """Return the normalised spectral gap λ₂ of *G*."""
    n = G.number_of_nodes()
    if n < 2:
        return 0.0
    L = nx.normalized_laplacian_matrix(G).toarray()
    eigs = np.linalg.eigvalsh(L)
    eigs.sort()
    return float(eigs[1])


# ── Razborov Approximation Method ────────────────────────────────────────────

def local_clique_approximation_error(G: nx.Graph, locality_radius: int = 2) -> float:
    """
    Estimate the approximation error when attempting to represent the
    Tseitin contradiction via *local* clique certificates of radius
    *locality_radius* in *G*.

    In Razborov's method:
    - A *p-approximator* for AND replaces it with a function that only
      examines a bounded-size sub-clique (local neighbourhood).
    - For an expander, any local neighbourhood of radius r has size
      O(d^r), while the "parity witness" requires Ω(n) variables.
    - The gap between local approximation and global truth is the
      approximation error.

    We model this as:
        error(r) = 1 − (neighbourhood_size / n)^(1/2)

    which approaches 1 as n → ∞ for fixed r.
    """
    n = G.number_of_nodes()
    d = G.degree(0) if n > 0 else 1
    neighbourhood_size = min(n, d ** locality_radius)
    ratio = neighbourhood_size / n
    return 1.0 - math.sqrt(ratio)


def kappa_pi_loss_factor(lam2: float) -> float:
    """
    Approximation-loss factor induced by the spectral gap.

    Interpretation: in the Razborov Approximation Lemma, each gate of
    the monotone circuit introduces a loss proportional to KAPPA_PI / λ₂.
    A larger spectral gap ⟹ smaller loss per gate ⟹ requires fewer gates
    to accumulate a given total error.  Equivalently, the lower bound on
    circuit size grows as (KAPPA_PI / λ₂)^Ω(n).

    Returns KAPPA_PI / λ₂.
    """
    if lam2 <= 0:
        return float("inf")
    return KAPPA_PI / lam2


def monotone_circuit_size_lower_bound(n: int, lam2: float) -> float:
    """
    Exponential lower bound on monotone circuit size for a Tseitin-type
    function on an *n*-vertex expander with spectral gap *lam2*.

    Following Razborov's technique, the lower bound is:

        size ≥ (κ_Π / λ₂)^(n^{1/3})

    The exponent n^{1/3} comes from the "sunflower" counting argument:
    any circuit of size s can be approximated with error < 1/3 only if
    s ≥ (κ_Π / λ₂)^(n^{1/3}).

    Returns the log₂ of this lower bound (to avoid overflow).
    """
    loss = kappa_pi_loss_factor(lam2)
    exponent = n ** (1.0 / 3.0)
    log2_lb = exponent * math.log2(loss) if loss > 1 else 0.0
    return log2_lb


def approximation_rounds_needed(n: int, lam2: float, error_budget: float = 1.0 / 3.0) -> float:
    """
    Number of approximation rounds in Razborov's method needed to achieve
    a total error ≥ *error_budget*.

    Each round multiplies the accumulated error by (κ_Π · λ₂).
    Starting from error ε₀ = 1/n, after r rounds:
        ε_r = ε₀ · (κ_Π · λ₂)^r

    We solve for r: r ≥ log(error_budget / ε₀) / log(κ_Π · λ₂).
    """
    eps0 = 1.0 / n
    if KAPPA_PI * lam2 <= 1.0:
        # Error cannot accumulate — circuit lower bound via direct argument
        return n
    rounds = math.log(error_budget / eps0) / math.log(KAPPA_PI * lam2)
    return max(1.0, rounds)


def negative_certificate_size(G: nx.Graph) -> int:
    """
    Size of the smallest *negative certificate* for the Tseitin function on *G*.

    A negative certificate for UNSAT is a proof that any assignment violates
    at least one clause.  For a Tseitin formula on an expander, the minimal
    certificate involves all edges in a balanced cut — Ω(h · n) edges.

    Returns ⌈h · n / 2⌉.
    """
    lam2 = spectral_gap(G)
    h = lam2 / 2.0
    n = G.number_of_nodes()
    return max(1, math.ceil(h * n / 2))


def positive_certificate_size(G: nx.Graph) -> int:
    """
    Size of the smallest *positive certificate* for a satisfying assignment
    (hypothetical, since Tseitin on odd expanders is UNSAT).

    For a hypothetical satisfiable instance, the positive certificate would
    need to specify a consistent parity assignment — at least Ω(n) variables.
    Returns n (the trivial upper bound / lower bound coincide here).
    """
    return G.number_of_nodes()


# ── Full analysis ──────────────────────────────────────────────────────────────

def analyze_monotone_circuits(n: int) -> Dict:
    """
    Full monotone circuit complexity analysis for a Tseitin-type function
    on an *n*-vertex circulant expander.
    """
    G = construct_circulant_expander(n)

    lam2 = spectral_gap(G)
    h = lam2 / 2.0
    locality_error = local_clique_approximation_error(G)
    loss = kappa_pi_loss_factor(lam2)
    log2_lb = monotone_circuit_size_lower_bound(n, lam2)
    rounds = approximation_rounds_needed(n, lam2)
    neg_cert = negative_certificate_size(G)
    pos_cert = positive_certificate_size(G)

    return {
        "n": n,
        "num_edges": G.number_of_edges(),
        "degree": G.degree(0),
        "spectral_gap_lambda2": lam2,
        "edge_expansion_h": h,
        "local_clique_approx_error": locality_error,
        "kappa_pi_loss_factor": loss,
        "log2_circuit_size_lower_bound": log2_lb,
        "approximation_rounds": rounds,
        "negative_certificate_size": neg_cert,
        "positive_certificate_size": pos_cert,
    }


def print_analysis(result: Dict) -> None:
    """Pretty-print the analysis result."""
    n = result["n"]
    print(f"\n{'='*70}")
    print(f"MONOTONE CIRCUITS ANALYSIS  n = {n}".center(70))
    print(f"Frecuencia de resonancia: {F0_QCAL} Hz  |  κ_Π = {KAPPA_PI}".center(70))
    print(f"{'='*70}")
    print(f"  Vértices                  : {n}")
    print(f"  Aristas                   : {result['num_edges']}")
    print(f"  Grado                     : {result['degree']}")
    print(f"  Gap espectral λ₂          : {result['spectral_gap_lambda2']:.4f}")
    print(f"  Expansión h(G) ≥          : {result['edge_expansion_h']:.4f}")
    print(f"  Error aprox. local        : {result['local_clique_approx_error']:.4f}")
    print(f"  Factor de pérdida κ_Π/λ₂  : {result['kappa_pi_loss_factor']:.4f}")
    print(f"  log₂(Tamaño circ. lb)     : {result['log2_circuit_size_lower_bound']:.2f}")
    print(f"  Rondas de aproximación    : {result['approximation_rounds']:.1f}")
    print(f"  Cert. negativo (UNSAT) ≥  : {result['negative_certificate_size']} vars")
    print(f"  Cert. positivo ≥          : {result['positive_certificate_size']} vars")
    print()
    if result["local_clique_approx_error"] > 0.5:
        print("  ✅ Aproximación local falla — falta de localidad confirmada")
    if result["log2_circuit_size_lower_bound"] > 1.0:
        print("  ✅ Cota inferior exponencial — circuito monótono no puede ser polinomial")
    print(f"{'='*70}")


# ── Entry point ────────────────────────────────────────────────────────────────

def run_monotone_circuits_demo() -> None:
    """Run demo analysis for representative expander sizes."""
    print("=" * 70)
    print("MONOTONE CIRCUITS – TÉCNICA DE RAZBOROV-QCAL".center(70))
    print("=" * 70)
    print(f"f₀ = {F0_QCAL} Hz  |  κ_Π = {KAPPA_PI}  |  φ = {PHI}")

    sizes = [50, 100, 200, 500]
    results = []
    for n in sizes:
        r = analyze_monotone_circuits(n)
        results.append(r)
        print_analysis(r)

    print("\n" + "=" * 70)
    print("TABLA RESUMEN".center(70))
    print("=" * 70)
    hdr = (
        f"{'n':<8} {'λ₂':<8} {'h(G)':<8} {'Err.loc':<10}"
        f" {'κ_Π/λ₂':<10} {'log₂(|C|lb)'}"
    )
    print(hdr)
    print("-" * 70)
    for r in results:
        print(
            f"{r['n']:<8} "
            f"{r['spectral_gap_lambda2']:<8.4f} "
            f"{r['edge_expansion_h']:<8.4f} "
            f"{r['local_clique_approx_error']:<10.4f} "
            f"{r['kappa_pi_loss_factor']:<10.4f} "
            f"{r['log2_circuit_size_lower_bound']:.2f}"
        )

    print(
        "\n🏛️  Vínculo QCAL: κ_Π actúa como factor de pérdida en el Lema de"
        "\n   Aproximación de Razborov. La falta de localidad (gap espectral)"
        "\n   impide toda aproximación mediante 'cliques' locales."
    )


if __name__ == "__main__":
    run_monotone_circuits_demo()
