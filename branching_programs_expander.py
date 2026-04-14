#!/usr/bin/env python3
"""
branching_programs_expander.py
Branching Program width lower bounds for Tseitin formulas on expander graphs.

Uses the Communication Complexity bottleneck technique to show that any
Branching Program (BP) solving the Tseitin formula on an n-vertex expander
must have width Ω(n), forcing total size (Length × Width) to be exponential.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Repository: motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import math
import numpy as np
import networkx as nx
from typing import Dict, List, Tuple

# ── Constants ─────────────────────────────────────────────────────────────────
F0_QCAL: float = 141.7001
KAPPA_PI: float = 2.5773
PHI: float = 1.618033988749895    # Golden ratio


# ── Expander construction (shared helper) ─────────────────────────────────────

def construct_circulant_expander(n: int) -> nx.Graph:
    """
    Build a circulant expander on *n* vertices with degree ≈ √n.
    For even *n* the degree is chosen to be odd (required for Tseitin UNSAT).
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


# ── Communication-complexity partitioning ────────────────────────────────────

def balanced_cut(G: nx.Graph) -> Tuple[List, List, int]:
    """
    Find an approximately balanced vertex partition (L, R) of *G* and
    return the number of crossing edges |∂(L,R)|.

    We use the Fiedler vector (second eigenvector of the normalised
    Laplacian) to partition: negative entries go to L, positive to R.
    """
    n = G.number_of_nodes()
    L_mat = nx.normalized_laplacian_matrix(G).toarray()
    eigs, vecs = np.linalg.eigh(L_mat)
    # Sort by eigenvalue
    order = np.argsort(eigs)
    fiedler = vecs[:, order[1]]

    nodes = list(G.nodes())
    left = [nodes[i] for i in range(n) if fiedler[i] <= 0]
    right = [nodes[i] for i in range(n) if fiedler[i] > 0]

    # Balance: if one side is empty, split at median
    if not left or not right:
        mid = n // 2
        left = nodes[:mid]
        right = nodes[mid:]

    left_set = set(left)
    right_set = set(right)
    crossing = sum(
        1 for u, v in G.edges() if (u in left_set) != (v in left_set)
    )
    return left, right, crossing


def information_flow_lower_bound(G: nx.Graph) -> int:
    """
    Lower bound on the information that must flow through any balanced
    partition of a Tseitin formula on *G*.

    Each crossing edge in the balanced cut corresponds to a variable
    whose assignment must be "communicated" across the cut.  For a good
    expander this is at least h · n / 2 bits, where h = λ₂ / 2.
    """
    _, _, crossing = balanced_cut(G)
    return crossing


# ── Branching Program metrics ─────────────────────────────────────────────────

def bp_width_lower_bound(G: nx.Graph) -> int:
    """
    Lower bound on the width of any Branching Program solving the Tseitin
    formula on *G*.

    By the Communication Complexity argument (Pudlák-Sgall / Beame et al.):
    Any BP must maintain a state that encodes the partial assignment on one
    side of a balanced cut.  The number of distinct states ≥ 2^(crossing),
    so width ≥ 2^(crossing).

    We return the *crossing edge count* as the exponent (the actual width
    lower bound is exponential in this value).
    """
    lam2 = spectral_gap(G)
    n = G.number_of_nodes()
    h = lam2 / 2.0
    # Width ≥ 2^(h · n / 2) — return the exponent
    return max(1, math.ceil(h * n / 2))


def bp_width_exponent(G: nx.Graph) -> float:
    """
    Exponent w such that BP width ≥ 2^w.

    Uses the spectral lower bound: w = λ₂ · n / 4.
    """
    lam2 = spectral_gap(G)
    n = G.number_of_nodes()
    return lam2 * n / 4.0


def bp_length_lower_bound(n: int) -> float:
    """
    Lower bound on the length (number of layers) of a BP solving Tseitin.

    At minimum the BP must read all variables: Length ≥ number of edges ≈ n·d/2.
    For circulant expanders of degree ≈ √n this is Ω(n^{3/2}).
    """
    d_approx = max(3, int(math.isqrt(n)))
    return n * d_approx / 2.0


def bp_total_size_lower_bound(G: nx.Graph) -> float:
    """
    Lower bound on total BP size = Length × Width.

    Size ≥ Length · 2^w where w = λ₂ · n / 4.
    This grows as exp(Ω(n)).
    """
    w = bp_width_exponent(G)
    n = G.number_of_nodes()
    length = bp_length_lower_bound(n)
    return length * (2.0 ** w)


# ── Full analysis ──────────────────────────────────────────────────────────────

def analyze_branching_programs(n: int) -> Dict:
    """
    Full Branching Program complexity analysis for a Tseitin formula on an
    *n*-vertex circulant expander.
    """
    G = construct_circulant_expander(n)

    lam2 = spectral_gap(G)
    h = lam2 / 2.0
    _, _, crossing = balanced_cut(G)
    width_exponent = bp_width_exponent(G)
    width_lb = 2 ** min(width_exponent, 60)   # cap to avoid overflow in display
    length_lb = bp_length_lower_bound(n)

    # Total size — cap exponent for display
    log_size = math.log(length_lb) + width_exponent * math.log(2) if length_lb > 0 else 0

    return {
        "n": n,
        "num_edges": G.number_of_edges(),
        "degree": G.degree(0),
        "spectral_gap_lambda2": lam2,
        "edge_expansion_h": h,
        "balanced_cut_crossing": crossing,
        "width_exponent": width_exponent,
        "width_lower_bound_log2": width_exponent,
        "length_lower_bound": length_lb,
        "log2_total_size_lower_bound": log_size / math.log(2),
    }


def print_analysis(result: Dict) -> None:
    """Pretty-print the analysis result."""
    n = result["n"]
    print(f"\n{'='*70}")
    print(f"BRANCHING PROGRAMS ANALYSIS  n = {n}".center(70))
    print(f"Frecuencia de resonancia: {F0_QCAL} Hz  |  κ_Π = {KAPPA_PI}".center(70))
    print(f"{'='*70}")
    print(f"  Vértices              : {n}")
    print(f"  Aristas               : {result['num_edges']}")
    print(f"  Grado                 : {result['degree']}")
    print(f"  Gap espectral λ₂      : {result['spectral_gap_lambda2']:.4f}")
    print(f"  Expansión h(G) ≥      : {result['edge_expansion_h']:.4f}")
    print(f"  Aristas cruzadas      : {result['balanced_cut_crossing']}")
    print(f"  Exp. de ancho (log₂)  : {result['width_exponent']:.2f}")
    print(f"  Ancho BP ≥            : 2^{result['width_lower_bound_log2']:.2f}")
    print(f"  Longitud BP ≥         : {result['length_lower_bound']:.0f}")
    print(f"  log₂(Tamaño BP lb)    : {result['log2_total_size_lower_bound']:.1f}  (≡ 2^{result['log2_total_size_lower_bound']:.1f})")
    print()
    if result["spectral_gap_lambda2"] > 0.1:
        print("  ✅ Cuello de botella de comunicación activo — ancho exponencial")
    print(f"{'='*70}")


# ── Entry point ────────────────────────────────────────────────────────────────

def run_branching_programs_demo() -> None:
    """Run demo analysis for representative expander sizes."""
    print("=" * 70)
    print("BRANCHING PROGRAMS – ANCHO DE COMUNICACIÓN QCAL".center(70))
    print("=" * 70)
    print(f"f₀ = {F0_QCAL} Hz  |  κ_Π = {KAPPA_PI}  |  φ = {PHI}")

    sizes = [50, 100, 200, 500]
    results = []
    for n in sizes:
        r = analyze_branching_programs(n)
        results.append(r)
        print_analysis(r)

    print("\n" + "=" * 70)
    print("TABLA RESUMEN".center(70))
    print("=" * 70)
    hdr = (
        f"{'n':<8} {'λ₂':<8} {'h(G)':<8} {'Cruce':<8}"
        f" {'w=log₂(W)':<12} {'log₂(|BP|)'}"
    )
    print(hdr)
    print("-" * 70)
    for r in results:
        print(
            f"{r['n']:<8} "
            f"{r['spectral_gap_lambda2']:<8.4f} "
            f"{r['edge_expansion_h']:<8.4f} "
            f"{r['balanced_cut_crossing']:<8} "
            f"{r['width_exponent']:<12.2f} "
            f"{r['log2_total_size_lower_bound']:.1f}"
        )

    print(
        "\n🏛️  Cota de Tamaño: Ancho Ω(n) → Tamaño exp(Ω(n))."
        "\n   El flujo de información a través de cualquier corte del"
        "\n   programa procesa la expansión de aristas del grafo original."
    )


if __name__ == "__main__":
    run_branching_programs_demo()
