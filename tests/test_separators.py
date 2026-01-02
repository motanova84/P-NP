#!/usr/bin/env python3
"""
test_separators.py
Validación empírica del teorema optimal_separator_exists
Autor: José Manuel Mota Burruezo Ψ ∞³ (Campo QCAL)
"""

import networkx as nx
import numpy as np
from typing import Set, Tuple, List

def find_balanced_separator_bfs(G: nx.Graph) -> Set:
    """
    Implementa findSeparatorBFS de Lean.
    Encuentra separador balanceado via BFS por niveles.
    """
    if len(G) == 0:
        return set()
    
    # Elegir raíz (vértice de grado máximo)
    root = max(G.nodes(), key=lambda v: G.degree(v))
    
    # BFS con niveles
    levels = {root: 0}
    queue = [root]
    max_level = 0
    
    while queue:
        v = queue.pop(0)
        for u in G.neighbors(v):
            if u not in levels:
                levels[u] = levels[v] + 1
                max_level = max(max_level, levels[u])
                queue.append(u)
    
    # Encontrar nivel que balancea componentes
    best_level = 0
    best_balance = float('inf')
    
    for L in range(max_level + 1):
        separator = {v for v, l in levels.items() if l == L}
        G_minus_S = G.copy()
        G_minus_S.remove_nodes_from(separator)
        
        components = list(nx.connected_components(G_minus_S))
        if len(components) == 0:
            continue
        
        max_comp = max(len(c) for c in components)
        balance = abs(max_comp - len(G) * 2 / 3)
        
        if balance < best_balance:
            best_balance = balance
            best_level = L
    
    separator = {v for v, l in levels.items() if l == best_level}
    return separator

def verify_separator_properties(G: nx.Graph, S: Set) -> Tuple[bool, int]:
    """
    Verifica que S es separador balanceado.
    Retorna (es_balanceado, tamaño_componente_máxima).
    """
    G_minus_S = G.copy()
    G_minus_S.remove_nodes_from(S)
    
    components = list(nx.connected_components(G_minus_S))
    max_comp_size = max(len(c) for c in components) if components else 0
    
    is_balanced = max_comp_size <= 2 * len(G) / 3
    
    return is_balanced, max_comp_size

def test_separator_theorem():
    """
    Valida teorema de separadores en casos concretos.
    """
    print("=" * 60)
    print("VALIDACIÓN EMPÍRICA: optimal_separator_exists")
    print("=" * 60)
    
    # Test 1: Grafo árbol (tw = 1)
    print("\n📊 Test 1: Árbol balanceado")
    T = nx.balanced_tree(2, 4)  # 31 nodos
    S = find_balanced_separator_bfs(T)
    is_bal, max_comp = verify_separator_properties(T, S)
    print(f"  Nodos: {len(T)}, tw ≈ 1")
    print(f"  Separador: |S| = {len(S)}")
    print(f"  Balanceado: {is_bal} (max comp: {max_comp})")
    print(f"  Bound esperado: tw + 1 = 2")
    print(f"  ✓ Cumple" if len(S) <= 2 else f"  ⚠️ Excede")
    
    # Test 2: Grafo grid (tw ≈ √n)
    print("\n📊 Test 2: Grid 10×10")
    Grid = nx.grid_2d_graph(10, 10)  # 100 nodos
    S_grid = find_balanced_separator_bfs(Grid)
    is_bal_grid, max_comp_grid = verify_separator_properties(Grid, S_grid)
    tw_grid = 10  # tw de grid n×n es ≈ n
    print(f"  Nodos: {len(Grid)}, tw ≈ {tw_grid}")
    print(f"  Separador: |S| = {len(S_grid)}")
    print(f"  Balanceado: {is_bal_grid} (max comp: {max_comp_grid})")
    print(f"  Bound esperado: tw + 1 = {tw_grid + 1}")
    print(f"  ✓ Cumple" if len(S_grid) <= tw_grid + 1 else f"  ⚠️ Excede")
    
    # Test 3: Grafo completo (tw = n-1, expansor)
    print("\n📊 Test 3: Grafo completo K₂₀")
    K20 = nx.complete_graph(20)
    S_complete = find_balanced_separator_bfs(K20)
    is_bal_complete, max_comp_complete = verify_separator_properties(K20, S_complete)
    tw_complete = 19
    print(f"  Nodos: {len(K20)}, tw = {tw_complete}")
    print(f"  Separador: |S| = {len(S_complete)}")
    print(f"  Balanceado: {is_bal_complete} (max comp: {max_comp_complete})")
    print(f"  Bound esperado: max(tw+1, n/2) = {max(tw_complete+1, 10)}")
    print(f"  ⚠️ Expansor: separador debe ser grande (≥ n/3)")
    
    # Test 4: Grafo CNF 3-SAT
    print("\n📊 Test 4: Grafo incidencia CNF (50 vars, 200 cláusulas)")
    G_cnf = nx.Graph()
    # Simular CNF: cada cláusula conectada a 3 variables aleatorias
    np.random.seed(42)
    for i in range(200):
        clause = f"C{i}"
        vars_in_clause = np.random.choice(50, 3, replace=False)
        for v in vars_in_clause:
            G_cnf.add_edge(f"x{v}", clause)
    
    S_cnf = find_balanced_separator_bfs(G_cnf)
    is_bal_cnf, max_comp_cnf = verify_separator_properties(G_cnf, S_cnf)
    tw_cnf_estimate = len(G_cnf) // 10  # Estimado
    print(f"  Nodos: {len(G_cnf)}, tw estimado ≈ {tw_cnf_estimate}")
    print(f"  Separador: |S| = {len(S_cnf)}")
    print(f"  Balanceado: {is_bal_cnf} (max comp: {max_comp_cnf})")
    
    print("\n" + "=" * 60)
    print("✅ TODOS LOS TESTS EJECUTADOS")
    print("=" * 60)

def test_golden_ratio_connection():
    """
    Prueba la conexión con la proporción áurea φ.
    """
    print("\n" + "=" * 60)
    print("CONEXIÓN CON LA PROPORCIÓN ÁUREA φ")
    print("=" * 60)
    
    phi = (1 + np.sqrt(5)) / 2
    print(f"\nφ = {phi:.6f}")
    print(f"φ² = {phi**2:.6f}")
    print(f"φ + 1 = {phi + 1:.6f}")
    print(f"Verificación: φ² = φ + 1? {abs(phi**2 - (phi + 1)) < 1e-10}")
    
    # Constante κ_Π relacionada
    kappa_pi = 2.5773
    print(f"\nκ_Π = {kappa_pi}")
    print(f"φ × (π/e) = {phi * (np.pi / np.e):.4f}")
    print(f"Relación con κ_Π: {abs(kappa_pi - phi * (np.pi / np.e)):.4f}")

if __name__ == "__main__":
    test_separator_theorem()
    test_golden_ratio_connection()
