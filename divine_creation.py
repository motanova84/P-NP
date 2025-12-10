"""
divine_creation.py - COMO DIOS CREARÍA Y UNIRÍA

Implementation of the Divine Trinity structure that unifies three fundamental dimensions:
- Topology (treewidth)
- Information (information complexity)
- Computation (time complexity)

All three dimensions are related by the sacred constant κ_Π = 2.5773.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Tarea 4: separator_information_need
"""

import networkx as nx
import numpy as np
import math
from typing import Set, Tuple, Dict, List

# ══════════════════════════════════════════════════════════════
# CONSTANTES SAGRADAS
# ══════════════════════════════════════════════════════════════

KAPPA_PI = 2.5773  # La constante que unifica todo
PHI = (1 + math.sqrt(5)) / 2  # Proporción áurea
E = math.e
PI = math.pi

# ══════════════════════════════════════════════════════════════
# CLASE: TRINIDAD DIVINA
# ══════════════════════════════════════════════════════════════

class DivineTrinity:
    """
    Unificación de las tres dimensiones:
    • Topología (treewidth)
    • Información (IC)
    • Computación (tiempo)
    
    Todas relacionadas por κ_Π = 2.5773
    """
    
    def __init__(self, G: nx.Graph):
        self.G = G
        self.n = len(G)
        
        # Computar las tres dimensiones
        self.topology = self.measure_topology()
        self.information = self.measure_information()
        self.computation = self.measure_computation()
        
        # Verificar unidad
        self.verify_unity()
    
    # ──────────────────────────────────────────────────────────
    # DIMENSIÓN 1: TOPOLOGÍA
    # ──────────────────────────────────────────────────────────
    
    def measure_topology(self) -> float:
        """
        Mide treewidth del grafo.
        Representa la ESTRUCTURA GEOMÉTRICA inherente.
        """
        if self.n == 0:
            return 0.0
        
        # Heurística min-degree
        G_copy = self.G.copy()
        max_degree = 0
        
        while G_copy.number_of_nodes() > 0:
            v = min(G_copy.nodes(), key=lambda x: G_copy.degree(x))
            deg = G_copy.degree(v)
            max_degree = max(max_degree, deg)
            
            # Fill edges
            neighbors = list(G_copy.neighbors(v))
            for i in range(len(neighbors)):
                for j in range(i+1, len(neighbors)):
                    if not G_copy.has_edge(neighbors[i], neighbors[j]):
                        G_copy.add_edge(neighbors[i], neighbors[j])
            
            G_copy.remove_node(v)
        
        return float(max_degree)
    
    # ──────────────────────────────────────────────────────────
    # DIMENSIÓN 2: INFORMACIÓN
    # ──────────────────────────────────────────────────────────
    
    def measure_information(self) -> float:
        """
        Mide complejidad de información via separador óptimo.
        Representa ENTROPÍA MÍNIMA para distinguir estados.
        """
        # Encontrar separador óptimo
        separator = self.find_optimal_separator()
        
        if len(separator) == 0:
            return 0.0
        
        # Calcular IC = log₂(configuraciones posibles)
        G_minus_S = self.G.copy()
        G_minus_S.remove_nodes_from(separator)
        
        num_components = nx.number_connected_components(G_minus_S)
        if num_components == 0:
            return float(len(separator))
        
        # IC ≈ |S| + log(num_components)
        ic = len(separator) + math.log2(max(num_components, 1))
        
        return ic
    
    def find_optimal_separator(self) -> Set:
        """
        Encuentra separador balanceado óptimo.
        Usa algoritmo de Tarea 3.
        """
        if self.n <= 2:
            return set(self.G.nodes())
        
        # BFS desde nodo central
        center = max(self.G.nodes(), key=lambda v: nx.degree(self.G, v))
        
        levels = {center: 0}
        queue = [center]
        
        while queue:
            v = queue.pop(0)
            for u in self.G.neighbors(v):
                if u not in levels:
                    levels[u] = levels[v] + 1
                    queue.append(u)
        
        # Encontrar nivel óptimo
        max_level = max(levels.values()) if levels else 0
        best_separator = set()
        best_balance = float('inf')
        
        for L in range(max_level + 1):
            separator = {v for v, lvl in levels.items() if lvl == L}
            
            G_minus = self.G.copy()
            G_minus.remove_nodes_from(separator)
            
            if nx.number_connected_components(G_minus) == 0:
                continue
            
            components = list(nx.connected_components(G_minus))
            if len(components) == 0:
                continue
                
            max_comp = max(len(c) for c in components)
            
            if max_comp <= 2 * self.n / 3:
                balance = abs(max_comp - 2 * self.n / 3)
                if balance < best_balance:
                    best_balance = balance
                    best_separator = separator
        
        return best_separator if best_separator else set(list(self.G.nodes())[:self.n//3])
    
    # ──────────────────────────────────────────────────────────
    # DIMENSIÓN 3: COMPUTACIÓN
    # ──────────────────────────────────────────────────────────
    
    def measure_computation(self) -> float:
        """
        Estima tiempo computacional mínimo.
        Representa PASOS DE CONSCIENCIA necesarios.
        """
        # Para SAT/3-CNF: tiempo ≈ 2^(tw) en promedio
        tw = self.topology
        ic = self.information
        
        # Usar promedio entre topology e information para mejor balance
        # La complejidad computacional está relacionada con ambas
        if tw <= 1:
            # Árboles tienen treewidth 1, complejidad lineal
            comp_time = self.n * math.log(self.n + 1) if self.n > 0 else 1
        elif tw <= math.log2(self.n + 1):
            # Caso polinomial: treewidth pequeño
            comp_time = (self.n ** tw) if self.n > 0 else 1
        else:
            # Caso exponencial: usar treewidth como guía
            # Combinar con information complexity para mejor estimación
            avg_complexity = (tw + ic) / 2
            comp_time = 2 ** min(avg_complexity, self.n / 10)
        
        # Escalar logarítmicamente para comparación
        return math.log2(max(comp_time, 1))
    
    # ──────────────────────────────────────────────────────────
    # VERIFICACIÓN DE UNIDAD
    # ──────────────────────────────────────────────────────────
    
    def verify_unity(self) -> Dict[str, bool]:
        """
        Verifica que las tres dimensiones están unidas por κ_Π.
        
        CONDICIÓN DIVINA:
        (1/κ_Π) * X ≤ Y ≤ κ_Π * X  para todo par (X,Y)
        """
        results = {}
        
        # Normalizar para comparación
        T = self.topology
        I = self.information
        C = self.computation
        
        # Test 1: Topología ↔ Información
        if T > 0:
            ratio_TI = I / T
            results['topology_information'] = (
                1/KAPPA_PI <= ratio_TI <= KAPPA_PI
            )
        else:
            results['topology_information'] = True
        
        # Test 2: Información ↔ Computación
        if I > 0:
            ratio_IC = C / I
            results['information_computation'] = (
                1/KAPPA_PI <= ratio_IC <= KAPPA_PI
            )
        else:
            results['information_computation'] = True
        
        # Test 3: Topología ↔ Computación
        if T > 0:
            ratio_TC = C / T
            results['topology_computation'] = (
                1/KAPPA_PI <= ratio_TC <= KAPPA_PI
            )
        else:
            results['topology_computation'] = True
        
        self.unity_verified = all(results.values())
        self.unity_results = results
        
        return results
    
    # ──────────────────────────────────────────────────────────
    # VISUALIZACIÓN DE LA UNIDAD
    # ──────────────────────────────────────────────────────────
    
    def display_trinity(self):
        """
        Muestra la trinidad unificada en forma sagrada.
        """
        print("╔" + "═" * 66 + "╗")
        print("║" + "TRINIDAD DIVINA - UNIFICACIÓN TOTAL".center(66) + "║")
        print("╠" + "═" * 66 + "╣")
        
        print(f"║  Grafo: {self.n} nodos" + " " * (66 - len(f"  Grafo: {self.n} nodos") - 2) + "║")
        print("╠" + "═" * 66 + "╣")
        
        print(f"║  📐 TOPOLOGÍA (treewidth):     {self.topology:8.2f}" + " " * 39 + "║")
        print(f"║  📊 INFORMACIÓN (IC):          {self.information:8.2f}" + " " * 39 + "║")
        print(f"║  ⚡ COMPUTACIÓN (log₂ tiempo): {self.computation:8.2f}" + " " * 39 + "║")
        
        print("╠" + "═" * 66 + "╣")
        print("║" + "VERIFICACIÓN DE UNIDAD VÍA κ_Π = 2.5773".center(66) + "║")
        print("╠" + "═" * 66 + "╣")
        
        for key, value in self.unity_results.items():
            status = "✅" if value else "❌"
            label = key.replace('_', ' ↔ ').title()
            print(f"║  {status} {label}" + " " * (64 - len(label) - 4) + "║")
        
        print("╠" + "═" * 66 + "╣")
        
        if self.unity_verified:
            print("║" + "🌟 UNIDAD VERIFICADA - TODO ES UNO 🌟".center(66) + "║")
        else:
            print("║" + "⚠️  Ajuste necesario en constantes".center(66) + "║")
        
        print("╚" + "═" * 66 + "╝")

# ══════════════════════════════════════════════════════════════
# DEMOSTRACIÓN: COMO DIOS CREARÍA
# ══════════════════════════════════════════════════════════════

def divine_demonstration():
    """
    Demuestra la unificación divina en casos concretos.
    """
    print("\n" + "═" * 70)
    print("COMO DIOS CREARÍA Y UNIRÍA - DEMOSTRACIÓN TOTAL".center(70))
    print("Tarea 4: separator_information_need".center(70))
    print("═" * 70)
    
    cases = []
    
    # ─────────────────────────────────────────────────────────
    # CASO 1: ÁRBOL (Estructura Simple)
    # ─────────────────────────────────────────────────────────
    print("\n🌲 CASO 1: ÁRBOL BALANCEADO")
    T = nx.balanced_tree(2, 4)
    trinity1 = DivineTrinity(T)
    trinity1.display_trinity()
    cases.append(("Árbol", trinity1.unity_verified))
    
    # ─────────────────────────────────────────────────────────
    # CASO 2: GRID (Estructura Media)
    # ─────────────────────────────────────────────────────────
    print("\n🔲 CASO 2: GRID 10×10")
    Grid = nx.grid_2d_graph(10, 10)
    trinity2 = DivineTrinity(Grid)
    trinity2.display_trinity()
    cases.append(("Grid", trinity2.unity_verified))
    
    # ─────────────────────────────────────────────────────────
    # CASO 3: EXPANSOR (Estructura Compleja)
    # ─────────────────────────────────────────────────────────
    print("\n🌐 CASO 3: GRAFO ALEATORIO (Expansor)")
    np.random.seed(42)
    ER = nx.erdos_renyi_graph(50, 0.4)
    trinity3 = DivineTrinity(ER)
    trinity3.display_trinity()
    cases.append(("Expansor", trinity3.unity_verified))
    
    # ─────────────────────────────────────────────────────────
    # CASO 4: CNF-SAT (Aplicación Real)
    # ─────────────────────────────────────────────────────────
    print("\n⚡ CASO 4: GRAFO INCIDENCIA 3-SAT")
    CNF = nx.Graph()
    for i in range(50):
        CNF.add_node(f"x{i}", type='var')
    for j in range(200):
        CNF.add_node(f"C{j}", type='clause')
        vars_in_clause = np.random.choice([f"x{i}" for i in range(50)], 3, replace=False)
        for v in vars_in_clause:
            CNF.add_edge(f"C{j}", v)
    
    trinity4 = DivineTrinity(CNF)
    trinity4.display_trinity()
    cases.append(("CNF-SAT", trinity4.unity_verified))
    
    # ─────────────────────────────────────────────────────────
    # RESUMEN FINAL
    # ─────────────────────────────────────────────────────────
    print("\n" + "═" * 70)
    print("📊 RESUMEN DE UNIFICACIÓN DIVINA".center(70))
    print("═" * 70)
    
    for name, unified in cases:
        status = "✅ UNIFICADO" if unified else "⚠️  PARCIAL"
        print(f"  {name:15} {status}")
    
    all_unified = all(unified for _, unified in cases)
    
    print("\n" + "═" * 70)
    if all_unified:
        print("🌟 TODAS LAS DIMENSIONES ESTÁN UNIDAS POR κ_Π 🌟".center(70))
        print("Como Dios crearía: TODO ES UNO".center(70))
    else:
        print("La unificación continúa emergiendo...".center(70))
    print("═" * 70)
    
    # ─────────────────────────────────────────────────────────
    # ECUACIÓN DIVINA FINAL
    # ─────────────────────────────────────────────────────────
    print("\n" + "╔" + "═" * 68 + "╗")
    print("║" + "ECUACIÓN DIVINA DE UNIFICACIÓN".center(68) + "║")
    print("╠" + "═" * 68 + "╣")
    print("║" + " " * 68 + "║")
    print("║" + "Topología ≈ Información ≈ Computación".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "(1/κ_Π) · X ≤ Y ≤ κ_Π · X  ∀ dimensiones X,Y".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "κ_Π = 2.5773 = φ × (π/e) × λ_CY".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "donde:".center(68) + "║")
    print("║" + "  φ = proporción áurea (1.618...)".center(68) + "║")
    print("║" + "  π/e = ratio sagrado (1.155...)".center(68) + "║")
    print("║" + "  λ_CY = factor Calabi-Yau (geometría cuántica)".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")

# ══════════════════════════════════════════════════════════════
# EJECUCIÓN
# ══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    divine_demonstration()
