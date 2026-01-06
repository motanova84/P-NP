#!/usr/bin/env python3
"""
Calculate Hodge Pairs Close to Golden Ratio Squared
====================================================

This script analyzes all pairs (h¹¹, h²¹) with N = h¹¹ + h²¹ ≤ 50
and identifies those where the ratio h¹¹/h²¹ is closest to φ² ≈ 2.6180339887.

This investigation explores the latent Fibonacci structure in Calabi-Yau
manifold Hodge numbers and their relationship to the golden ratio.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 6, 2026
"""

import sympy as sp
import numpy as np
import sys
from typing import List, Tuple


def calculate_pairs_close_to_phi_squared(max_n: int = 50) -> List[Tuple]:
    """
    Calculate all pairs (h11, h21) with N = h11 + h21 ≤ max_n
    and compute their distance to φ².
    
    Args:
        max_n: Maximum value of N = h11 + h21
        
    Returns:
        List of tuples (N, h11, h21, ratio, distance) sorted by distance
    """
    # Define golden ratio phi and its square
    phi = (1 + sp.sqrt(5)) / 2
    phi_sq = phi**2
    
    print("=" * 80)
    print("Cálculo de Pares de Hodge Cercanos a φ²")
    print("=" * 80)
    print()
    print(f"φ (razón áurea) = (1 + √5)/2 = {float(phi):.10f}")
    print(f"φ² = φ + 1 = {float(phi_sq):.10f}")
    print()
    print(f"Generando todos los pares (h¹¹, h²¹) con N = h¹¹ + h²¹ ≤ {max_n}")
    print()
    
    # Generate all pairs (h11, h21) with N = h11 + h21 ≤ max_n
    results = []
    for N in range(3, max_n + 1):  # Start from N=3 (minimum meaningful)
        for h11 in range(1, N):  # h11 must be at least 1 and less than N
            h21 = N - h11
            if h21 < 1:  # h21 must also be at least 1
                continue
            
            # Calculate ratio h11/h21
            ratio = sp.Rational(h11, h21)
            
            # Calculate distance to φ²
            diff = abs(ratio - phi_sq)
            
            results.append((N, h11, h21, float(ratio), float(diff)))
    
    # Sort by distance to φ² (ascending)
    results_sorted = sorted(results, key=lambda x: x[4])
    
    print(f"Total de pares generados: {len(results)}")
    print()
    
    return results_sorted


def display_top_10_pairs(results: List[Tuple], phi_sq: float):
    """
    Display the top 10 pairs closest to φ².
    
    Args:
        results: Sorted list of (N, h11, h21, ratio, distance) tuples
        phi_sq: Value of φ²
    """
    print("=" * 80)
    print("Top 10 Pares Más Cercanos a φ² ≈ 2.6180339887")
    print("=" * 80)
    print()
    
    # Display header
    header = f"{'N = h¹¹ + h²¹':<15} {'h¹¹':<6} {'h²¹':<6} {'h¹¹/h²¹':<14} {'|h¹¹/h²¹ − φ²|':<20}"
    print(header)
    print("-" * 80)
    
    # Display top 10
    top10 = results[:10]
    for N, h11, h21, ratio, diff in top10:
        print(f"{N:<15} {h11:<6} {h21:<6} {ratio:<14.10f} {diff:<20.10f}")
    
    print("=" * 80)
    print()
    
    return top10


def analyze_fibonacci_structure(top10: List[Tuple]):
    """
    Analyze the Fibonacci structure in the top 10 pairs.
    
    Args:
        top10: List of top 10 (N, h11, h21, ratio, distance) tuples
    """
    print("=" * 80)
    print("Análisis de Estructura Fibonacci")
    print("=" * 80)
    print()
    
    print("Observaciones:")
    print()
    
    # Check for Fibonacci numbers
    fibonacci = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
    
    print("1. Presencia de Números de Fibonacci:")
    for N, h11, h21, ratio, diff in top10:
        fib_in_h11 = "✓" if h11 in fibonacci else " "
        fib_in_h21 = "✓" if h21 in fibonacci else " "
        if fib_in_h11 or fib_in_h21:
            print(f"   N={N:2d}: h¹¹={h11:2d} [{fib_in_h11}], h²¹={h21:2d} [{fib_in_h21}]  "
                  f"→  ratio = {ratio:.10f}")
    
    print()
    print("2. Par Más Cercano:")
    N, h11, h21, ratio, diff = top10[0]
    print(f"   (h¹¹, h²¹) = ({h11}, {h21}) con N = {N}")
    print(f"   Ratio h¹¹/h²¹ = {ratio:.10f}")
    print(f"   Distancia a φ² = {diff:.10f}")
    
    if h11 in fibonacci and h21 in fibonacci:
        print(f"   ✓ Ambos {h11} y {h21} son números de Fibonacci!")
    
    print()
    print("3. Convergencia hacia φ²:")
    print("   Los siguientes pares más cercanos muestran una convergencia hacia φ²,")
    print("   sugiriendo una estructura armónica relacionada con la proporción áurea.")
    print()
    
    # Check if ratios of consecutive Fibonacci numbers appear
    fib_ratios = []
    for i in range(len(fibonacci) - 1):
        if fibonacci[i+1] > 0:
            fib_ratios.append((fibonacci[i+1], fibonacci[i], fibonacci[i+1] / fibonacci[i]))
    
    print("4. Ratios de Fibonacci Consecutivos:")
    for h11, h21, ratio in fib_ratios[3:10]:  # Skip first few that are far from phi
        print(f"   {h11}/{h21} = {ratio:.10f}")
    
    print()
    print("=" * 80)
    print()


def statistical_analysis(results: List[Tuple], phi_sq: float):
    """
    Perform statistical analysis on the distribution of pairs.
    
    Args:
        results: Full list of (N, h11, h21, ratio, distance) tuples
        phi_sq: Value of φ²
    """
    print("=" * 80)
    print("Análisis Estadístico")
    print("=" * 80)
    print()
    
    # Extract distances
    distances = np.array([r[4] for r in results])
    ratios = np.array([r[3] for r in results])
    
    print(f"Total de pares analizados: {len(results)}")
    print()
    
    # Bins for clustering analysis
    bins = [0.01, 0.05, 0.1, 0.2, 0.5, 1.0]
    print("Distribución por Cercanía a φ²:")
    for i in range(len(bins)):
        if i == 0:
            count = np.sum(distances < bins[i])
            print(f"  |h¹¹/h²¹ − φ²| < {bins[i]:<5.2f}: {count:4d} pares")
        else:
            count = np.sum((distances >= bins[i-1]) & (distances < bins[i]))
            print(f"  {bins[i-1]:<5.2f} ≤ |h¹¹/h²¹ − φ²| < {bins[i]:<5.2f}: {count:4d} pares")
    
    count_far = np.sum(distances >= bins[-1])
    print(f"  |h¹¹/h²¹ − φ²| ≥ {bins[-1]:<5.2f}: {count_far:4d} pares")
    print()
    
    # Statistics
    print("Estadísticas de Ratios:")
    print(f"  Media:              {np.mean(ratios):.6f}")
    print(f"  Mediana:            {np.median(ratios):.6f}")
    print(f"  Desviación estándar: {np.std(ratios):.6f}")
    print(f"  Valor φ²:           {phi_sq:.6f}")
    print()
    
    print("=" * 80)
    print()


def implication_analysis():
    """
    Discuss implications of the Fibonacci structure in Calabi-Yau manifolds.
    """
    print("=" * 80)
    print("Implicaciones")
    print("=" * 80)
    print()
    
    print("Esta estructura sugiere:")
    print()
    print("1. ESTRUCTURA FIBONÁCCICA LATENTE:")
    print("   Los pares (h¹¹, h²¹) que mejor aproximan φ² frecuentemente contienen")
    print("   números de Fibonacci, sugiriendo una estructura armónica subyacente.")
    print()
    
    print("2. RELACIÓN CON BASES DE DATOS REALES:")
    print("   Se podría buscar acumulación estadística en torno a φ² en las bases")
    print("   de datos de variedades Calabi-Yau como Kreuzer-Skarke.")
    print()
    
    print("3. MINIMIZACIÓN DE ENERGÍA:")
    print("   Estas estructuras podrían minimizar energía o complejidad topológica,")
    print("   ofreciendo una explicación física o algorítmica para su prevalencia.")
    print()
    
    print("4. CONEXIÓN CON κ_Π = 2.5773:")
    print("   La constante universal κ_Π podría relacionarse con esta estructura")
    print("   armónica a través de la geometría espectral de las variedades CY.")
    print()
    
    print("=" * 80)
    print()


def main():
    """Main execution function."""
    # Calculate all pairs and sort by distance to φ²
    results_sorted = calculate_pairs_close_to_phi_squared(max_n=50)
    
    # Get φ² value
    phi = (1 + sp.sqrt(5)) / 2
    phi_sq = float(phi**2)
    
    # Display top 10
    top10 = display_top_10_pairs(results_sorted, phi_sq)
    
    # Analyze Fibonacci structure
    analyze_fibonacci_structure(top10)
    
    # Statistical analysis
    statistical_analysis(results_sorted, phi_sq)
    
    # Discuss implications
    implication_analysis()
    
    print("✓ Análisis completado exitosamente")
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
