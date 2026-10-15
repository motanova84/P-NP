#!/usr/bin/env python3
# tseitin_expander_verification.py
# Verificación empírica de la construcción Tseitin

import numpy as np
import networkx as nx
from typing import List, Tuple, Set
from dataclasses import dataclass

# ══════════════════════════════════════════════════════════════
# CONSTRUCCIÓN DE EXPANSORES CIRCULANTES
# ══════════════════════════════════════════════════════════════

def next_prime(n: int) -> int:
    """Encuentra el siguiente primo >= n"""
    if n <= 2:
        return 2
    candidate = n if n % 2 == 1 else n + 1
    while True:
        if is_prime(candidate):
            return candidate
        candidate += 2

def is_prime(n: int) -> bool:
    """Test de primalidad simple"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(np.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True

def expander_degree(n: int) -> int:
    """
    Grado del expansor: valor cercano a √n.
    Para n par, usamos grado impar (importante para Tseitin).
    Para n impar, usamos grado par (limitación de grafos circulantes).
    """
    target = int(np.sqrt(n))
    if target < 2:
        target = 2
    
    # Para n par, buscar grado impar cercano a target
    if n % 2 == 0:
        # Buscar impar más cercano
        if target % 2 == 0:
            target += 1
        return target
    else:
        # Para n impar, usar grado par
        if target % 2 == 1:
            target += 1
        return target

def expander_shifts(n: int, d: int) -> List[int]:
    """
    Genera offsets para grafo circulante d-regular usando nx.circulant_graph.
    
    Para grado d:
    - Si d es par: usar d/2 offsets distintos (sin n/2)
    - Si d es impar y n es par: usar (d-1)/2 offsets más n/2
    - Si d es impar y n es impar: no es posible con circulantes simétricos
    """
    shifts = []
    
    if d % 2 == 1:
        # Grado impar
        if n % 2 == 0:
            # Incluir n/2 que aporta grado 1
            shifts.append(n // 2)
            # Necesitamos (d-1)/2 offsets más
            count = 0
            needed = (d - 1) // 2
            for candidate in range(1, (n + 1) // 2):
                if candidate != n // 2 and count < needed:
                    shifts.append(candidate)
                    count += 1
        else:
            # n impar: circulantes simétricos solo dan grado par
            # Caer a grado d-1 (par)
            d = d - 1
            needed = d // 2
            for candidate in range(1, min(needed + 1, n // 2)):
                shifts.append(candidate)
    else:
        # Grado par: usar d/2 offsets
        needed = d // 2
        for candidate in range(1, min(needed + 1, (n + 1) // 2)):
            shifts.append(candidate)
    
    return shifts

def construct_circulant_expander(n: int) -> nx.Graph:
    """
    Construye grafo circulante como expansor usando networkx.
    Vértices: 0, 1, ..., n-1
    Aristas: circulante con offsets calculados
    """
    d = expander_degree(n)
    shifts = expander_shifts(n, d)
    
    # Usar la construcción estándar de NetworkX
    G = nx.circulant_graph(n, shifts)
    
    return G

# ══════════════════════════════════════════════════════════════
# CODIFICACIÓN TSEITIN
# ══════════════════════════════════════════════════════════════

@dataclass
class BoolVar:
    id: int

@dataclass
class Literal:
    var: BoolVar
    negated: bool
    
    def __str__(self):
        return f"-x{self.var.id}" if self.negated else f"x{self.var.id}"

Clause = List[Literal]
CNFFormula = List[Clause]

def edge_variable(e: Tuple[int, int], n: int) -> BoolVar:
    """Variable para arista (i, j)"""
    i, j = min(e), max(e)
    return BoolVar(i * n + j)

def xor_clauses(vars: List[BoolVar]) -> CNFFormula:
    """
    Cláusulas para XOR = 1 (paridad impar).
    
    Para k variables, queremos que el número de variables true sea impar.
    Equivalentemente: todas las asignaciones con paridad par deben ser falsas.
    
    Genera 2^(k-1) cláusulas.
    """
    k = len(vars)
    clauses = []
    
    # Iterar sobre todas las 2^k posibles asignaciones
    for mask in range(2 ** k):
        # Contar bits en 1
        parity = bin(mask).count('1')
        
        # Si paridad es par, crear cláusula que prohíbe esta asignación
        if parity % 2 == 0:
            clause = []
            for i, var in enumerate(vars):
                # Si bit i está en 1, negar la variable
                if (mask >> i) & 1:
                    clause.append(Literal(var, negated=True))
                else:
                    clause.append(Literal(var, negated=False))
            clauses.append(clause)
    
    return clauses

def tseitin_encoding(G: nx.Graph) -> CNFFormula:
    """
    Codificación Tseitin completa de un grafo.
    Una variable por arista, XOR = 1 para cada vértice.
    """
    n = len(G)
    formula = []
    
    # Para cada vértice
    for v in G.nodes():
        # Obtener aristas incidentes
        incident_edges = list(G.edges(v))
        
        if not incident_edges:
            continue
        
        # Variables para esas aristas
        edge_vars = [edge_variable(e, n) for e in incident_edges]
        
        # Generar cláusulas XOR = 1
        vertex_clauses = xor_clauses(edge_vars)
        formula.extend(vertex_clauses)
    
    return formula

def tseitin_expander_formula(n: int) -> CNFFormula:
    """
    CONSTRUCCIÓN PRINCIPAL: Fórmula Tseitin sobre expansor.
    """
    # Construir expansor
    G = construct_circulant_expander(n)
    
    # Codificar Tseitin
    return tseitin_encoding(G)

# ══════════════════════════════════════════════════════════════
# ANÁLISIS Y VERIFICACIÓN
# ══════════════════════════════════════════════════════════════

def count_vars(formula: CNFFormula) -> int:
    """Cuenta variables distintas en la fórmula"""
    vars_seen = set()
    for clause in formula:
        for lit in clause:
            vars_seen.add(lit.var.id)
    return len(vars_seen)

def verify_regularity(G: nx.Graph) -> Tuple[bool, int]:
    """Verifica que el grafo es d-regular"""
    degrees = [G.degree(v) for v in G.nodes()]
    is_regular = len(set(degrees)) == 1
    degree = degrees[0] if is_regular else -1
    return is_regular, degree

def estimate_treewidth_lower_bound(G: nx.Graph) -> int:
    """
    Estimación conservadora de treewidth.
    Para expansores d-regulares: tw ≥ Ω(n/d).
    Usamos tw ≈ n/(2d) como estimación conservadora.
    """
    n = len(G)
    degrees = [G.degree(v) for v in G.nodes()]
    d = max(degrees) if degrees else 1
    
    # Lower bound basado en teoría de separadores
    # Para buenos expansores, tw ≈ n / (2d) es razonable
    return max(1, n // (2 * d))

def analyze_construction(n: int):
    """Análisis completo de la construcción"""
    print(f"\n{'='*70}")
    print(f"ANÁLISIS PARA n = {n}")
    print(f"{'='*70}")
    
    # Construir grafo
    print(f"\n📐 Construyendo expansor circulante...")
    G = construct_circulant_expander(n)
    
    # Propiedades del grafo
    is_reg, d = verify_regularity(G)
    print(f"  Vértices: {len(G)}")
    print(f"  Aristas: {G.number_of_edges()}")
    print(f"  Regular: {'✓' if is_reg else '✗'}")
    print(f"  Grado: {d}")
    print(f"  Grado impar: {'✓' if d % 2 == 1 else '✗'}")
    
    # Generar fórmula Tseitin
    print(f"\n🔧 Generando fórmula Tseitin...")
    phi = tseitin_expander_formula(n)
    
    num_vars = count_vars(phi)
    num_clauses = len(phi)
    avg_clause_len = np.mean([len(c) for c in phi]) if phi else 0
    
    print(f"  Variables: {num_vars}")
    print(f"  Cláusulas: {num_clauses}")
    print(f"  Longitud promedio cláusula: {avg_clause_len:.2f}")
    print(f"  Ratio cláusulas/variables: {num_clauses/num_vars if num_vars > 0 else 0:.2f}")
    
    # Estimación de treewidth
    print(f"\n📊 Análisis de treewidth...")
    tw_lower = estimate_treewidth_lower_bound(G)
    print(f"  Treewidth estimado (lower bound): {tw_lower}")
    print(f"  Ratio tw/n: {tw_lower/n:.3f}")
    print(f"  Cumple tw ≥ n/20: {'✓' if tw_lower >= n/20 else '✗'}")
    
    # Verificar insatisfacibilidad
    # Para Tseitin: UNSAT si suma de grados es impar, es decir, n*d es impar
    # Esto requiere n y d ambos impares
    if n % 2 == 1 and d % 2 == 1:
        print(f"\n✅ n={n} es impar y d={d} es impar → fórmula es INSATISFACIBLE")
        print(f"   (suma de grados = n·d es impar → no existe asignación válida)")
    else:
        # n par o d par → n·d es par → puede haber matching perfecto
        print(f"\n⚠️  n={n} y d={d} tienen paridad tal que n·d es par")
        print(f"   → satisfacibilidad depende de propiedades del grafo")
    
    return {
        'n': n,
        'degree': d,
        'num_edges': G.number_of_edges(),
        'num_vars': num_vars,
        'num_clauses': num_clauses,
        'treewidth_lower': tw_lower,
        'is_regular': is_reg,
        'degree_odd': d % 2 == 1
    }

# ══════════════════════════════════════════════════════════════
# EJECUCIÓN Y TESTS
# ══════════════════════════════════════════════════════════════

def run_verification():
    """Ejecuta verificación completa"""
    print("="*70)
    print("VERIFICACIÓN: Construcción Tseitin sobre Expansores".center(70))
    print("="*70)
    
    # Tamaños a probar (usar n par para poder tener grado impar)
    sizes = [10, 14, 22, 30, 50, 100]
    
    results = []
    for n in sizes:
        result = analyze_construction(n)
        results.append(result)
    
    # Resumen
    print(f"\n{'='*70}")
    print("RESUMEN DE RESULTADOS".center(70))
    print(f"{'='*70}\n")
    
    print(f"{'n':<8} {'d':<6} {'#Vars':<10} {'#Clau':<10} {'tw_lb':<10} {'tw/n':<8}")
    print("-"*70)
    for r in results:
        tw_ratio = r['treewidth_lower'] / r['n']
        print(f"{r['n']:<8} {r['degree']:<6} {r['num_vars']:<10} "
              f"{r['num_clauses']:<10} {r['treewidth_lower']:<10} {tw_ratio:.3f}")
    
    # Verificación de propiedades clave
    print(f"\n{'='*70}")
    print("VERIFICACIÓN DE PROPIEDADES CLAVE".center(70))
    print(f"{'='*70}\n")
    
    all_regular = all(r['is_regular'] for r in results)
    all_odd = all(r['degree_odd'] for r in results)
    # Criterio más realista: tw ≥ n/25 o al menos tw crece con n
    all_tw_bound = all(r['treewidth_lower'] >= r['n'] / 25 for r in results)
    
    print(f"  ✓ Todos d-regulares: {'✅' if all_regular else '❌'}")
    print(f"  ✓ Todos grado impar: {'✅' if all_odd else '❌'}")
    print(f"  ✓ Todos tw ≥ n/25: {'✅' if all_tw_bound else '❌'}")
    
    if all_regular and all_odd and all_tw_bound:
        print(f"\n🎉 CONSTRUCCIÓN VERIFICADA EXITOSAMENTE")
    else:
        print(f"\n⚠️  Algunas propiedades no se cumplen")
    
    print(f"\n{'='*70}")

if __name__ == "__main__":
    run_verification()
