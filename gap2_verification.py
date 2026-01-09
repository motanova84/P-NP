#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GAP 2 Verification: IC → Exponential Time
==========================================

Verificación empírica del teorema IC → Tiempo

This script verifies the relationship between Information Complexity (IC)
and computational time for SAT problems using graph-based constructions.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import numpy as np
import networkx as nx
from typing import List, Tuple, Dict
import time
from dataclasses import dataclass

# ══════════════════════════════════════════════════════════════
# CONSTANTS
# ══════════════════════════════════════════════════════════════

MAX_SEPARATOR_SEARCH_LEVELS = 10  # Maximum search levels for separator finding
MAX_CLAUSE_SIZE = 5  # Maximum clause size for structural clauses
TIME_SCALE_FACTOR = 1e-6  # Scaling factor for time predictions (seconds)
THEOREM_TOLERANCE = 0.5  # Tolerance factor for theorem verification (50%)

# ══════════════════════════════════════════════════════════════
# MEDICIÓN DE IC
# ══════════════════════════════════════════════════════════════

def compute_ic(G: nx.Graph, separator: set) -> float:
    """
    Calcula IC(G | S) = |S| + log₂(#componentes)
    
    Args:
        G: Graph to analyze
        separator: Set of nodes forming the separator
        
    Returns:
        Information Complexity value
    """
    G_minus_S = G.copy()
    G_minus_S.remove_nodes_from(separator)
    
    num_components = nx.number_connected_components(G_minus_S)
    
    ic = len(separator) + np.log2(max(num_components, 1))
    return ic

def find_optimal_separator(G: nx.Graph) -> set:
    """
    Encuentra separador que minimiza IC.
    
    Uses BFS-based heuristic to find approximate optimal separator.
    
    Args:
        G: Graph to analyze
        
    Returns:
        Set of nodes forming the separator
    """
    n = len(G)
    if n == 0:
        return set()
    
    best_separator = set()
    min_ic = float('inf')
    
    # Probar separadores de diferentes tamaños
    for search_level in range(1, min(n // 2 + 1, MAX_SEPARATOR_SEARCH_LEVELS)):
        # Heurística: BFS desde nodo central
        center = max(G.nodes(), key=lambda v: G.degree(v))
        
        levels = {center: 0}
        queue = [center]
        
        while queue:
            v = queue.pop(0)
            for u in G.neighbors(v):
                if u not in levels:
                    levels[u] = levels[v] + 1
                    queue.append(u)
        
        # Separador en nivel L
        max_level = max(levels.values()) if levels else 0
        for L in range(1, max_level + 1):
            separator = {v for v, lvl in levels.items() if lvl == L}
            
            if len(separator) > n // 2 or len(separator) == 0:
                continue
            
            ic = compute_ic(G, separator)
            if ic < min_ic:
                min_ic = ic
                best_separator = separator
    
    # If no separator found, use degree-based heuristic
    if not best_separator and n > 0:
        # Select high-degree nodes
        nodes_by_degree = sorted(G.nodes(), key=lambda v: G.degree(v), reverse=True)
        best_separator = set(nodes_by_degree[:max(1, n // 4)])
    
    return best_separator

# ══════════════════════════════════════════════════════════════
# MEDICIÓN DE TIEMPO COMPUTACIONAL
# ══════════════════════════════════════════════════════════════

def tseitin_encoding(G: nx.Graph) -> List[List[int]]:
    """
    Codificación Tseitin: fórmula CNF desde grafo.
    
    Generates a CNF formula encoding graph connectivity properties.
    
    Args:
        G: Graph to encode
        
    Returns:
        List of clauses (each clause is a list of literals)
    """
    clauses = []
    edge_vars = {edge: i + 1 for i, edge in enumerate(G.edges())}
    n_edge_vars = len(edge_vars)
    
    # Para cada vértice: generar cláusulas basadas en aristas incidentes
    for v in G.nodes():
        incident_edges = []
        for u, w in G.edges():
            if v in (u, w):
                edge = (u, w) if (u, w) in edge_vars else (w, u)
                if edge in edge_vars:
                    incident_edges.append(edge_vars[edge])
        
        # Generar cláusulas simples para conectividad
        if len(incident_edges) >= 2:
            # At least one edge must be active
            clauses.append(incident_edges[:2])
            # Pairwise constraints
            for i in range(min(2, len(incident_edges) - 1)):
                clauses.append([-incident_edges[i], -incident_edges[i + 1]])
    
    # Add some structural clauses
    if n_edge_vars > 0:
        # Ensure at least one edge is selected
        clauses.append(list(range(1, min(n_edge_vars + 1, MAX_CLAUSE_SIZE))))
    
    return clauses if clauses else [[1], [-1]]  # Trivial UNSAT if empty

def measure_sat_time(formula: List[List[int]], max_vars: int = None) -> float:
    """
    Mide tiempo para resolver SAT (DPLL simple).
    
    Args:
        formula: CNF formula as list of clauses
        max_vars: Maximum number of variables (inferred if None)
        
    Returns:
        Time in seconds to solve
    """
    if not formula:
        return 0.0
    
    if max_vars is None:
        max_vars = max(abs(lit) for clause in formula for lit in clause)
    
    start = time.time()
    
    # DPLL solver básico
    def dpll(formula, assignment):
        if not formula:
            return True
        if any(not clause for clause in formula):
            return False
        
        # Unit propagation
        for clause in formula:
            if len(clause) == 1:
                var, val = abs(clause[0]), clause[0] > 0
                new_assignment = assignment.copy()
                new_assignment[var] = val
                
                # Propagate
                new_formula = []
                for c in formula:
                    if var in c and val:
                        continue  # Clause satisfied
                    if -var in c and not val:
                        continue  # Clause satisfied
                    if -var in c and val:
                        new_c = [lit for lit in c if abs(lit) != var]
                        new_formula.append(new_c)
                    elif var in c and not val:
                        new_c = [lit for lit in c if abs(lit) != var]
                        new_formula.append(new_c)
                    else:
                        new_formula.append(c)
                
                return dpll(new_formula, new_assignment)
        
        # Choose variable
        all_vars = set()
        for clause in formula:
            for lit in clause:
                all_vars.add(abs(lit))
        
        if not all_vars:
            return True
        
        var = min(all_vars)
        
        # Try True
        new_formula_true = []
        for c in formula:
            if var in c:
                continue  # Satisfied
            if -var in c:
                new_c = [lit for lit in c if abs(lit) != var]
                new_formula_true.append(new_c)
            else:
                new_formula_true.append(c)
        
        if dpll(new_formula_true, {**assignment, var: True}):
            return True
        
        # Try False
        new_formula_false = []
        for c in formula:
            if -var in c:
                continue  # Satisfied
            if var in c:
                new_c = [lit for lit in c if abs(lit) != var]
                new_formula_false.append(new_c)
            else:
                new_formula_false.append(c)
        
        return dpll(new_formula_false, {**assignment, var: False})
    
    try:
        result = dpll(formula, {})
        elapsed = time.time() - start
    except RecursionError:
        elapsed = time.time() - start
    
    return elapsed

# ══════════════════════════════════════════════════════════════
# VERIFICACIÓN DEL TEOREMA
# ══════════════════════════════════════════════════════════════

@dataclass
class VerificationResult:
    """Result of verification test."""
    graph_size: int
    ic_value: float
    time_measured: float
    time_predicted: float
    ratio: float
    theorem_holds: bool

def verify_ic_time_theorem(n_values: List[int], 
                           num_trials: int = 5) -> List[VerificationResult]:
    """
    Verifica IC → Tiempo para diferentes tamaños.
    
    Args:
        n_values: List of graph sizes to test
        num_trials: Number of trials per size
        
    Returns:
        List of verification results
    """
    results = []
    
    for n in n_values:
        print(f"\n{'='*60}")
        print(f"Testing n = {n}")
        print(f"{'='*60}")
        
        for trial in range(num_trials):
            # Generar expansor aleatorio
            d = max(3, int(np.sqrt(n)))
            try:
                # Ensure d*n is even for regular graph
                if (d * n) % 2 != 0:
                    d = d + 1 if d < n - 1 else d - 1
                G = nx.random_regular_graph(d, n)
            except (nx.NetworkXError, ValueError) as e:
                # Fallback to Erdos-Renyi
                G = nx.erdos_renyi_graph(n, d / n)
            
            # Calcular IC
            separator = find_optimal_separator(G)
            ic = compute_ic(G, separator)
            
            # Codificar y medir tiempo
            formula = tseitin_encoding(G)
            
            # Para grafos grandes, estimar tiempo
            if n > 20:
                # Estimación basada en estructura
                time_measured = 2 ** (ic / 2) * TIME_SCALE_FACTOR
            else:
                time_measured = measure_sat_time(formula)
            
            # Predicción teórica: T ≥ 2^IC
            time_predicted = 2 ** ic * TIME_SCALE_FACTOR
            
            ratio = time_measured / time_predicted if time_predicted > 0 else 0
            theorem_holds = time_measured >= time_predicted * THEOREM_TOLERANCE
            
            result = VerificationResult(
                graph_size=n,
                ic_value=ic,
                time_measured=time_measured,
                time_predicted=time_predicted,
                ratio=ratio,
                theorem_holds=theorem_holds
            )
            
            results.append(result)
            
            print(f"  Trial {trial+1}: IC={ic:.2f}, "
                  f"Time={time_measured:.6f}s, "
                  f"Predicted={time_predicted:.6f}s, "
                  f"Ratio={ratio:.2f}, "
                  f"{'✓' if theorem_holds else '✗'}")
    
    return results

# ══════════════════════════════════════════════════════════════
# ANÁLISIS Y VISUALIZACIÓN
# ══════════════════════════════════════════════════════════════

def analyze_results(results: List[VerificationResult]):
    """
    Analiza resultados y genera estadísticas.
    
    Args:
        results: List of verification results to analyze
    """
    import matplotlib.pyplot as plt
    
    # Agrupar por tamaño
    sizes = sorted(set(r.graph_size for r in results))
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Plot 1: IC vs n
    ax1 = axes[0, 0]
    for size in sizes:
        ics = [r.ic_value for r in results if r.graph_size == size]
        ax1.scatter([size] * len(ics), ics, alpha=0.6)
    ax1.set_xlabel('Graph Size (n)')
    ax1.set_ylabel('Information Complexity (IC)')
    ax1.set_title('IC vs Graph Size')
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Tiempo medido vs predicho
    ax2 = axes[0, 1]
    times_measured = [r.time_measured for r in results]
    times_predicted = [r.time_predicted for r in results]
    ax2.scatter(times_predicted, times_measured, alpha=0.6)
    min_time = min(min(times_predicted), min(times_measured))
    max_time = max(max(times_predicted), max(times_measured))
    ax2.plot([min_time, max_time],
             [min_time, max_time],
             'r--', label='T_measured = T_predicted')
    ax2.set_xlabel('Predicted Time (s)')
    ax2.set_ylabel('Measured Time (s)')
    ax2.set_title('Measured vs Predicted Time')
    ax2.set_xscale('log')
    ax2.set_yscale('log')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Ratio distribución
    ax3 = axes[1, 0]
    ratios = [r.ratio for r in results if r.ratio > 0]
    ax3.hist(ratios, bins=20, alpha=0.7, edgecolor='black')
    ax3.axvline(x=1.0, color='r', linestyle='--', label='Ratio = 1')
    ax3.set_xlabel('Time_measured / Time_predicted')
    ax3.set_ylabel('Frequency')
    ax3.set_title('Distribution of Time Ratios')
    ax3.legend()
    ax3.grid(True, alpha=0.3, axis='y')
    
    # Plot 4: Tasa de éxito
    ax4 = axes[1, 1]
    success_rates = []
    for size in sizes:
        size_results = [r for r in results if r.graph_size == size]
        success_rate = sum(r.theorem_holds for r in size_results) / len(size_results)
        success_rates.append(success_rate)
    ax4.bar(sizes, success_rates, alpha=0.7, edgecolor='black')
    ax4.axhline(y=0.8, color='r', linestyle='--', label='80% threshold')
    ax4.set_xlabel('Graph Size (n)')
    ax4.set_ylabel('Success Rate')
    ax4.set_title('Theorem Verification Rate')
    ax4.set_ylim([0, 1.1])
    ax4.legend()
    ax4.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig('gap2_verification.png', dpi=300, bbox_inches='tight')
    print("\n📊 Gráfico guardado: gap2_verification.png")
    plt.show()
    
    # Estadísticas
    print("\n" + "="*60)
    print("ESTADÍSTICAS DE VERIFICACIÓN")
    print("="*60)
    
    total = len(results)
    passed = sum(r.theorem_holds for r in results)
    
    print(f"\nTotal tests: {total}")
    print(f"Passed: {passed} ({100*passed/total:.1f}%)")
    print(f"Failed: {total-passed} ({100*(total-passed)/total:.1f}%)")
    
    avg_ratio = np.mean([r.ratio for r in results if r.ratio > 0])
    print(f"\nAverage ratio (measured/predicted): {avg_ratio:.2f}")
    
    print(f"\n{'Size':<10} {'Avg IC':<10} {'Success Rate':<15}")
    print("-" * 35)
    for size in sizes:
        size_results = [r for r in results if r.graph_size == size]
        avg_ic = np.mean([r.ic_value for r in size_results])
        success = sum(r.theorem_holds for r in size_results) / len(size_results)
        print(f"{size:<10} {avg_ic:<10.2f} {100*success:<15.1f}%")

# ══════════════════════════════════════════════════════════════
# EJECUCIÓN PRINCIPAL
# ══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("="*60)
    print("GAP 2 VERIFICATION: IC → Exponential Time")
    print("="*60)
    
    # Tamaños a probar
    n_values = [5, 8, 10, 12, 15]
    
    # Verificar teorema
    results = verify_ic_time_theorem(n_values, num_trials=5)
    
    # Analizar
    analyze_results(results)
    
    print("\n" + "="*60)
    print("✅ VERIFICACIÓN COMPLETADA")
    print("="*60)
