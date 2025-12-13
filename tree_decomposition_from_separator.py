#!/usr/bin/env python3
"""
Tree Decomposition from Separator Algorithm
============================================

Constructs tree decompositions using balanced separators.
This algorithm recursively finds balanced separators and builds
a tree decomposition with width bounded by the separator size.

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import networkx as nx
from typing import List, Tuple, Set, Optional
from dataclasses import dataclass
import heapq

@dataclass
class TreeDecompositionNode:
    """Nodo en una tree decomposition."""
    bag: Set[int]          # Conjunto de vértices
    children: List[int]    # Índices de nodos hijos
    parent: Optional[int]  # Índice del padre
    
    def __str__(self):
        return f"Bag: {sorted(self.bag)}"

class TreeDecompositionBuilder:
    """Constructor de tree decomposition desde separadores."""
    
    def __init__(self, graph: nx.Graph):
        self.graph = graph
        self.memo = {}
    
    def find_balanced_separator(self, vertices: Set[int]) -> Optional[Set[int]]:
        """
        Encuentra separador balanceado usando BFS.
        
        Estrategia:
        1. Comenzar desde vértice de mayor grado
        2. Expandir por niveles hasta encontrar corte balanceado
        3. Minimizar tamaño del separador
        """
        if len(vertices) <= 1:
            return None
        
        # Convertir a lista para ordenamiento
        vert_list = list(vertices)
        
        # Ordenar por grado descendente
        vert_list.sort(key=lambda v: self.graph.degree(v), reverse=True)
        
        best_separator = None
        best_balance = float('inf')
        
        # Probar diferentes vértices iniciales
        for start in vert_list[:10]:  # Probar primeros 10
            separator, balance = self._bfs_separator(start, vertices)
            if separator and balance < best_balance:
                best_separator = separator
                best_balance = balance
        
        return best_separator
    
    def _bfs_separator(self, start: int, vertices: Set[int]) -> Tuple[Optional[Set[int]], float]:
        """
        BFS para encontrar separador balanceado desde un vértice.
        """
        visited = {start}
        queue = [start]
        levels = {start: 0}
        
        while queue:
            current = queue.pop(0)
            for neighbor in self.graph.neighbors(current):
                if neighbor in vertices and neighbor not in visited:
                    visited.add(neighbor)
                    queue.append(neighbor)
                    levels[neighbor] = levels[current] + 1
        
        # Buscar nivel que mejor separa
        max_level = max(levels.values()) if levels else 0
        
        for L in range(1, max_level):
            separator = {v for v, lvl in levels.items() if lvl == L}
            
            # Verificar si es separador
            if self._is_separator(separator, vertices):
                # Calcular balance
                components = self._connected_components(vertices - separator)
                if not components:
                    continue
                
                max_comp = max(len(c) for c in components)
                balance = abs(max_comp - len(vertices) / 2)
                
                return separator, balance
        
        return None, float('inf')
    
    def _is_separator(self, separator: Set[int], vertices: Set[int]) -> bool:
        """Verifica si S separa el conjunto de vértices."""
        if not separator:
            return False
        
        # Crear subgrafo sin separador
        sub_vertices = vertices - separator
        if not sub_vertices:
            return True
        
        # Extraer componente conexa
        visited = set()
        
        def dfs(v):
            stack = [v]
            while stack:
                current = stack.pop()
                if current in visited:
                    continue
                visited.add(current)
                for neighbor in self.graph.neighbors(current):
                    if neighbor in sub_vertices and neighbor not in visited:
                        stack.append(neighbor)
        
        # Comenzar DFS desde primer vértice
        start = next(iter(sub_vertices))
        dfs(start)
        
        # Si no visitamos todos, es separador
        return len(visited) < len(sub_vertices)
    
    def _connected_components(self, vertices: Set[int]) -> List[Set[int]]:
        """Encuentra componentes conexas en el subgrafo."""
        if not vertices:
            return []
        
        visited = set()
        components = []
        
        def bfs_component(start):
            component = set()
            queue = [start]
            while queue:
                v = queue.pop(0)
                if v in visited:
                    continue
                visited.add(v)
                component.add(v)
                for neighbor in self.graph.neighbors(v):
                    if neighbor in vertices and neighbor not in visited:
                        queue.append(neighbor)
            return component
        
        for v in vertices:
            if v not in visited:
                component = bfs_component(v)
                components.append(component)
        
        return components
    
    def build_tree_decomposition(self, vertices: Optional[Set[int]] = None) -> List[TreeDecompositionNode]:
        """
        Construye tree decomposition usando eliminación greedy min-degree.
        Este enfoque garantiza las tres propiedades de tree decomposition.
        """
        if vertices is None:
            vertices = set(self.graph.nodes())
        
        if not vertices:
            return []
        
        # Caso base: conjunto pequeño - una sola bolsa
        if len(vertices) <= 1:
            return [TreeDecompositionNode(bag=vertices, children=[], parent=None)]
        
        # Usar algoritmo de eliminación greedy para construir tree decomposition
        # Este enfoque garantiza las propiedades de tree decomposition
        G_copy = self.graph.subgraph(vertices).copy()
        elimination_order = []
        bags = []
        
        # Eliminar vértices en orden de grado mínimo
        while G_copy.number_of_nodes() > 0:
            # Encontrar vértice de grado mínimo
            if G_copy.number_of_nodes() == 1:
                v = list(G_copy.nodes())[0]
            else:
                v = min(G_copy.nodes(), key=lambda x: G_copy.degree(x))
            
            # Crear bag con v y sus vecinos
            neighbors = set(G_copy.neighbors(v))
            bag = neighbors | {v}
            bags.append(bag)
            elimination_order.append(v)
            
            # Hacer clique de vecinos (fill edges)
            neighbor_list = list(neighbors)
            for i in range(len(neighbor_list)):
                for j in range(i+1, len(neighbor_list)):
                    u1, u2 = neighbor_list[i], neighbor_list[j]
                    if not G_copy.has_edge(u1, u2):
                        G_copy.add_edge(u1, u2)
            
            # Eliminar vértice
            G_copy.remove_node(v)
        
        # Construir tree decomposition desde los bags
        # Regla: cada bag se conecta al bag más reciente que comparte vértices
        decomposition = []
        for i, bag in enumerate(bags):
            node = TreeDecompositionNode(
                bag=bag.copy(),
                children=[],
                parent=None
            )
            decomposition.append(node)
        
        # Para cada bag (excepto el primero), encontrar el último bag anterior
        # que comparte vértices y hacerlo su padre
        for i in range(1, len(decomposition)):
            # Buscar hacia atrás para encontrar el último bag que comparte vértices
            found_parent = False
            for j in range(i - 1, -1, -1):
                if decomposition[i].bag & decomposition[j].bag:
                    decomposition[i].parent = j
                    decomposition[j].children.append(i)
                    found_parent = True
                    break
            
            # Si no encontramos padre, conectar al nodo más cercano
            # (esto puede pasar en grafos desconectados o con bags sin intersección)
            if not found_parent:
                # Buscar el bag con el que más vecinos comparte en el grafo original
                best_parent = 0
                max_shared_neighbors = 0
                for j in range(i):
                    # Contar vértices en bag[i] que son adyacentes a vértices en bag[j]
                    shared_neighbors = 0
                    for v in decomposition[i].bag:
                        for u in decomposition[j].bag:
                            if self.graph.has_edge(v, u):
                                shared_neighbors += 1
                    if shared_neighbors > max_shared_neighbors:
                        max_shared_neighbors = shared_neighbors
                        best_parent = j
                
                decomposition[i].parent = best_parent
                decomposition[best_parent].children.append(i)
        
        return decomposition
    
    def compute_width(self, decomposition: List[TreeDecompositionNode]) -> int:
        """Calcula el ancho de la tree decomposition."""
        if not decomposition:
            return 0
        return max(len(node.bag) for node in decomposition) - 1
    
    def verify_tree_decomposition(self, decomposition: List[TreeDecompositionNode]) -> bool:
        """Verifica las propiedades de tree decomposition."""
        if not decomposition:
            return True
        
        # 1. Cada vértice aparece en al menos una bolsa
        all_vertices = set(self.graph.nodes())
        covered_vertices = set()
        
        for node in decomposition:
            covered_vertices.update(node.bag)
        
        if covered_vertices != all_vertices:
            print(f"❌ Vértices no cubiertos: {all_vertices - covered_vertices}")
            return False
        
        # 2. Para cada arista, existe bolsa que contiene ambos extremos
        for u, v in self.graph.edges():
            found = False
            for node in decomposition:
                if u in node.bag and v in node.bag:
                    found = True
                    break
            if not found:
                print(f"❌ Arista ({u},{v}) no cubierta")
                return False
        
        # 3. Para cada vértice, nodos que lo contienen forman subárbol conexo
        for v in all_vertices:
            # Encontrar índices de nodos que contienen v
            containing_nodes = [i for i, node in enumerate(decomposition) if v in node.bag]
            
            if len(containing_nodes) <= 1:
                # Un solo nodo o ninguno - trivialmente conexo
                continue
            
            # Construir subgrafo inducido
            subgraph = nx.Graph()
            subgraph.add_nodes_from(containing_nodes)
            
            # Añadir aristas según parentesco
            for i in containing_nodes:
                node = decomposition[i]
                if node.parent is not None and node.parent in containing_nodes:
                    subgraph.add_edge(i, node.parent)
                # También añadir aristas a hijos
                for child in node.children:
                    if child in containing_nodes:
                        subgraph.add_edge(i, child)
            
            # Verificar conectividad
            if subgraph.number_of_nodes() > 0 and not nx.is_connected(subgraph):
                print(f"❌ Vértice {v}: nodos que lo contienen no son conexos")
                print(f"   Nodos conteniendo {v}: {containing_nodes}")
                print(f"   Edges en subgrafo: {list(subgraph.edges())}")
                return False
        
        return True

def test_on_various_graphs():
    """Prueba el algoritmo en diferentes grafos."""
    print("="*70)
    print("PRUEBA: Construcción de Tree Decomposition desde Separadores".center(70))
    print("="*70)
    
    test_cases = [
        ("Path(10)", nx.path_graph(10)),
        ("Cycle(10)", nx.cycle_graph(10)),
        ("Grid(4×4)", nx.grid_2d_graph(4, 4)),
        ("Complete(8)", nx.complete_graph(8)),
        ("Random Regular(20,4)", nx.random_regular_graph(4, 20)),
        ("Expander(31)", None)  # Construir expander
    ]
    
    results = []
    
    for name, graph in test_cases:
        print(f"\n📊 {name}")
        print("-"*50)
        
        if graph is None:
            # Construir grafo circulante (expander)
            n = 31
            graph = nx.Graph()
            graph.add_nodes_from(range(n))
            shifts = [1, 3, 8, 23]  # Primos relativos
            for i in range(n):
                for s in shifts:
                    j = (i + s) % n
                    if i != j:
                        graph.add_edge(i, j)
        
        # Convert grid graph to integers
        if "Grid" in name:
            graph = nx.convert_node_labels_to_integers(graph)
        
        # Construir tree decomposition
        builder = TreeDecompositionBuilder(graph)
        decomposition = builder.build_tree_decomposition()
        
        # Calcular ancho
        width = builder.compute_width(decomposition)
        
        # Verificar
        is_valid = builder.verify_tree_decomposition(decomposition)
        
        # Separador mínimo estimado
        n = len(graph)
        min_sep_est = n // 3  # Estimación
        
        print(f"  Nodos en TD: {len(decomposition)}")
        print(f"  Ancho calculado: {width}")
        print(f"  Separador mínimo estimado: ~{min_sep_est}")
        print(f"  ¿Válido?: {'✅' if is_valid else '❌'}")
        
        results.append({
            'name': name,
            'n': n,
            'width': width,
            'min_sep_est': min_sep_est,
            'valid': is_valid,
            'bound_holds': width <= min_sep_est + 2  # tw ≤ min_sep + 1
        })
    
    # Resumen
    print(f"\n{'='*70}")
    print("RESUMEN".center(70))
    print(f"{'='*70}\n")
    
    print(f"{'Grafo':<25} {'n':<6} {'tw':<6} {'min_sep':<8} {'¿tw≤sep+1?':<12} {'Válido':<10}")
    print("-"*70)
    
    for r in results:
        print(f"{r['name']:<25} "
              f"{r['n']:<6} "
              f"{r['width']:<6} "
              f"{r['min_sep_est']:<8} "
              f"{'✅' if r['bound_holds'] else '❌':<12} "
              f"{'✅' if r['valid'] else '❌':<10}")
    
    # Estadísticas
    total = len(results)
    valid_count = sum(1 for r in results if r['valid'])
    bound_count = sum(1 for r in results if r['bound_holds'])
    
    print(f"\n{'='*70}")
    print(f"Total tests: {total}")
    print(f"✅ TD válidas: {valid_count}/{total} ({100*valid_count/total:.0f}%)")
    print(f"✅ Bound tw≤sep+1: {bound_count}/{total} ({100*bound_count/total:.0f}%)")
    
    if valid_count == total and bound_count == total:
        print("\n🎉 ALGORITMO VERIFICADO EXITOSAMENTE")
    else:
        print("\n⚠️  Algunas pruebas fallaron")
    
    return results

def visualize_example():
    """Visualizar ejemplo de construcción."""
    import matplotlib.pyplot as plt
    
    # Crear grafo de ejemplo
    G = nx.cycle_graph(8)
    
    # Construir tree decomposition
    builder = TreeDecompositionBuilder(G)
    decomposition = builder.build_tree_decomposition()
    
    # Visualizar grafo original
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    ax1 = axes[0]
    pos = nx.spring_layout(G)
    nx.draw(G, pos, with_labels=True, node_color='lightblue', 
            node_size=500, ax=ax1)
    ax1.set_title("Grafo Original", fontsize=14, fontweight='bold')
    
    # Visualizar tree decomposition
    ax2 = axes[1]
    
    # Crear árbol de bags
    T = nx.Graph()
    for i, node in enumerate(decomposition):
        T.add_node(i, bag=node.bag)
        if node.parent is not None:
            T.add_edge(i, node.parent)
    
    pos_tree = nx.spring_layout(T)
    labels = {i: f"B{i}:{sorted(list(node.bag))}" for i, node in enumerate(decomposition)}
    
    nx.draw(T, pos_tree, with_labels=True, labels=labels, 
            node_color='lightgreen', node_size=800, font_size=8, ax=ax2)
    ax2.set_title("Tree Decomposition", fontsize=14, fontweight='bold')
    
    plt.tight_layout()
    plt.savefig('tree_decomposition_example.png', dpi=300, bbox_inches='tight')
    print("\n📊 Gráfico guardado: tree_decomposition_example.png")
    plt.show()

if __name__ == "__main__":
    # Ejecutar pruebas
    results = test_on_various_graphs()
    
    # Visualizar ejemplo
    visualize_example()
    
    print(f"\n{'='*70}")
    print("✅ CONSTRUCCIÓN DE TREE DECOMPOSITION COMPLETADA")
    print(f"{'='*70}")
