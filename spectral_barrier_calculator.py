#!/usr/bin/env python3
"""
Calculador de Barrera Espectral (QCAL-Rigor)
=============================================

Implementa el cálculo del Expansion-Width Bound para fórmulas de Tseitin
sobre grafos de Ramanujan. El gap espectral (λ₂) del grafo dicta el
lower bound real en el modelo de Resolución, utilizando κ_Π como el
puente de traducción (Ben-Sasson & Wigderson).

Teorema de Rigidez de Tseitin (QCAL-Beta):
    Para toda familia de grafos expanders con gap espectral λ > 0,
    el tamaño de la refutación por resolución de la fórmula de Tseitin
    asociada crece exponencialmente con la expansión del grafo,
    sellado por el invariante topológico κ_Π.

    Size ≥ exp(κ_Π · w² / n)

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³
"""

import numpy as np
import networkx as nx

# Constante topológica κ_Π (coeficiente de rigidez estructural)
from qcal.constants import KAPPA_PI


def analyze_spectral_barrier(n_nodes: int = 100, d_degree: int = 3) -> dict:
    """
    Calcula la barrera espectral de un grafo de Ramanujan-like.

    Genera un grafo d-regular aleatorio, calcula su gap espectral (λ₂),
    y deriva la cota inferior de complejidad de resolución para la fórmula
    de Tseitin asociada.

    Parámetros
    ----------
    n_nodes : int
        Número de nodos del grafo (n_nodes * d_degree debe ser par).
    d_degree : int
        Grado de regularidad del grafo.

    Retorna
    -------
    dict con las claves:
        - spectral_gap        : float  – λ₂ (segundo valor propio del Laplaciano)
        - expansion_estimate  : float  – cota inferior de Cheeger (λ₂ / 2)
        - width_bound         : float  – ancho mínimo de resolución
        - complexity_lower_bound : float – cota inferior de tamaño de refutación
    """
    # 1. Generar un Grafo Ramanujan-like (d-regular aleatorio)
    G = nx.random_regular_graph(d_degree, n_nodes, seed=42)

    # 2. Matriz Laplaciana y valores propios
    L = nx.laplacian_matrix(G).toarray()
    eigenvalues = np.sort(np.linalg.eigvals(L).real)

    # Gap Espectral (λ₂): medida de conectividad global
    spectral_gap = float(eigenvalues[1])

    # 3. Traducción a Complejidad de Resolución (Ben-Sasson & Wigderson)
    # El ancho (width) es proporcional a la expansión (h_G)
    expansion_estimate = spectral_gap / 2  # Cota inferior de Cheeger
    width_bound = (expansion_estimate * n_nodes) / (2 * d_degree)

    # 4. Invariante QCAL (κ_Π) como factor de escala de resolución
    # Complejidad ≥ exp(κ_Π · w² / n)
    complexity_lower_bound = float(np.exp(KAPPA_PI * (width_bound ** 2) / n_nodes))

    return {
        "spectral_gap": spectral_gap,
        "expansion_estimate": expansion_estimate,
        "width_bound": width_bound,
        "complexity_lower_bound": complexity_lower_bound,
    }


def print_spectral_analysis(n_nodes: int = 100, d_degree: int = 3) -> None:
    """Imprime el análisis completo de la barrera espectral."""
    print("=" * 70)
    print("CALCULADOR DE BARRERA ESPECTRAL (QCAL-Rigor)".center(70))
    print(f"f₀ = 141.7001 Hz  |  κ_Π = {KAPPA_PI}".center(70))
    print("=" * 70)

    res = analyze_spectral_barrier(n_nodes, d_degree)

    print(f"\nGrafo Ramanujan-like: {n_nodes} nodos, {d_degree}-regular")
    print(f"\n  Gap Espectral (λ₂):              {res['spectral_gap']:.4f}")
    print(f"  Estimación de Expansión (h_G):   {res['expansion_estimate']:.4f}")
    print(f"  Ancho Mínimo de Resolución (w):  {res['width_bound']:.4f}")
    print(f"  Lower Bound (Size):              {res['complexity_lower_bound']:.2e}")

    print("\n" + "=" * 70)
    print("Lema (Barrera de Alon-QCAL):".center(70))
    print("  Size ≥ exp(κ_Π · w² / n)".center(70))
    print("=" * 70 + "\n")


if __name__ == "__main__":
    # Análisis de 100 nodos (demostración base)
    print_spectral_analysis(100, 3)

    # Análisis escalado a 1000 nodos
    print_spectral_analysis(1000, 3)
