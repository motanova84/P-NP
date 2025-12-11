# kappa_verification.py
import numpy as np
import networkx as nx
from scipy.sparse.linalg import eigsh
import matplotlib.pyplot as plt

def construct_tseitin_incidence(n: int, d: int = 8) -> nx.Graph:
    """Construir grafo de incidencia de Tseitin sobre expander."""
    # Grafo expander base (simulado)
    base_G = nx.random_regular_graph(d, n)
    
    # Grafo de incidencia bipartito
    I = nx.Graph()
    
    # Nodos: cláusulas (0..n-1) y variables (n..n+edges-1)
    clauses = list(range(n))
    edges = list(base_G.edges())
    variables = list(range(n, n + len(edges)))
    
    I.add_nodes_from(clauses, bipartite=0)
    I.add_nodes_from(variables, bipartite=1)
    
    # Conectar: cada cláusula con sus aristas incidentes
    # Normalize edges to have smaller node first to avoid ordering issues
    edge_to_var = {}
    for i, e in enumerate(edges):
        normalized_edge = tuple(sorted(e))
        edge_to_var[normalized_edge] = i + n
    
    for v in range(n):
        incident_edges = base_G.edges(v)
        for e in incident_edges:
            normalized_edge = tuple(sorted(e))
            var = edge_to_var[normalized_edge]
            I.add_edge(v, var)
    
    return I, base_G

def compute_spectral_constant(G: nx.Graph) -> float:
    """Calcular kappa_Pi = 1/(1 - lambda_2/sqrt(d_avg*(d_avg-1))).
    
    Note: This uses non-normalized adjacency matrix eigenvalues, which
    can lead to negative kappa values for bipartite graphs where
    lambda_2 is large relative to sqrt(d_avg*(d_avg-1)).
    """
    # Get degrees
    degrees = np.array([d for _, d in G.degree()])
    d_avg = np.mean(degrees)
    
    # Get non-normalized adjacency matrix
    A = nx.adjacency_matrix(G).toarray()
    
    # Compute eigenvalues of adjacency matrix (not normalized)
    eigenvalues = np.linalg.eigvalsh(A)
    eigenvalues = np.sort(eigenvalues)[::-1]  # Orden descendente
    
    # lambda_2 (segundo más grande) - this is the actual adjacency eigenvalue
    lambda_2 = eigenvalues[1] if len(eigenvalues) > 1 else 0
    
    # kappa formula using non-normalized lambda_2
    denominator_term = np.sqrt(d_avg * (d_avg - 1))
    
    # Check if lambda_2 >= sqrt(d_avg * (d_avg - 1))
    if lambda_2 >= denominator_term:
        # This causes negative kappa - the critical issue!
        kappa = 1.0 / (1 - lambda_2 / denominator_term)
        return kappa  # Will be negative
    else:
        kappa = 1.0 / (1 - lambda_2 / denominator_term)
        return kappa

def verify_kappa_decay(max_n: int = 500, step: int = 50):
    """Verificar que kappa decae como O(1/(sqrt(n) log n)).
    
    Note: For Tseitin incidence graphs, kappa often becomes negative,
    which reveals a fundamental flaw in the lower bound approach.
    """
    results = []
    
    for n in range(100, max_n, step):
        if n % 2 == 0:
            n += 1  # Hacer impar
        
        try:
            I, _ = construct_tseitin_incidence(n, d=8)
            kappa = compute_spectral_constant(I)
            
            # Keep all results, including negative kappa values
            # This is the key insight - negative kappa invalidates the bound
            bound = 2.0 / (np.sqrt(5*n) * np.log(5*n))  # 5n vértices totales
            ratio = kappa / bound
            results.append((n, kappa, bound, ratio))
        except Exception as e:
            print(f"Error con n={n}: {e}")
            continue
    
    return results

def plot_results(results):
    """Graficar resultados."""
    if not results:
        print("No hay resultados para graficar")
        return
    
    ns = [r[0] for r in results]
    kappas = [r[1] for r in results]
    bounds = [r[2] for r in results]
    ratios = [r[3] for r in results]
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Plot 1: kappa vs n
    ax1 = axes[0, 0]
    ax1.loglog(ns, kappas, 'bo-', label='kappa_Pi observado', alpha=0.7)
    ax1.loglog(ns, bounds, 'r--', label='Bound: 2/(sqrt(n) log n)', linewidth=2)
    ax1.set_xlabel('n (tamaño del grafo base)', fontsize=12)
    ax1.set_ylabel('kappa_Pi', fontsize=12)
    ax1.set_title('Decaimiento de kappa_Pi', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Ratio kappa/bound
    ax2 = axes[0, 1]
    ax2.semilogx(ns, ratios, 'gs-', markersize=8, alpha=0.7)
    ax2.axhline(y=1.0, color='r', linestyle='--', label='Límite teórico')
    ax2.set_xlabel('n', fontsize=12)
    ax2.set_ylabel('Ratio: kappa / bound', fontsize=12)
    ax2.set_title('Verificación del Bound', fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: kappa en escala lineal
    ax3 = axes[1, 0]
    ax3.plot(ns, kappas, 'mo-', label='kappa_Pi', alpha=0.7)
    ax3.plot(ns, [2.954] * len(ns), 'r--', label='Límite biregular perfecto: 2.954')
    ax3.set_xlabel('n', fontsize=12)
    ax3.set_ylabel('kappa_Pi', fontsize=12)
    ax3.set_title('kappa_Pi vs Límite Teórico', fontsize=14, fontweight='bold')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Predicción IC
    ax4 = axes[1, 1]
    # IC estimado = sqrt(n) / (2*kappa)
    ic_estimates = [np.sqrt(n) / (2 * max(kappa, 0.001)) for n, kappa in zip(ns, kappas)]
    ic_lower_bound = [0.01 * n * np.log(n) for n in ns]
    
    ax4.loglog(ns, ic_estimates, 'co-', label='IC estimado = sqrt(n)/(2*kappa)', alpha=0.7)
    ax4.loglog(ns, ic_lower_bound, 'm--', label='Límite deseado: 0.01·n·log n', linewidth=2)
    ax4.set_xlabel('n', fontsize=12)
    ax4.set_ylabel('Information Complexity (estimada)', fontsize=12)
    ax4.set_title('IC Estimado del Lower Bound', fontsize=14, fontweight='bold')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('kappa_verification_results.png', dpi=300, bbox_inches='tight')
    plt.show()
    
    # Estadísticas
    print("\n" + "="*70)
    print("RESUMEN ESTADÍSTICO".center(70))
    print("="*70)
    
    avg_ratio = np.mean(ratios)
    min_ratio = np.min(ratios)
    max_ratio = np.max(ratios)
    
    print(f"\nMuestra: {len(results)} tamaños de n")
    print(f"Ratio promedio kappa/bound: {avg_ratio:.4f}")
    print(f"Ratio mínimo: {min_ratio:.4f}")
    print(f"Ratio máximo: {max_ratio:.4f}")
    
    # Check if kappa values are negative (critical issue)
    if any(kappa < 0 for _, kappa, _, _ in results):
        print("\n⚠️  ¡PROBLEMA CRÍTICO DETECTADO!")
        print("   kappa_Pi es NEGATIVO para estos grafos de incidencia de Tseitin")
        print(f"   Esto invalida la cota inferior IC >= tw/(2*kappa)")
        print(f"   Promedio kappa_Pi: {np.mean([kappa for _, kappa, _, _ in results]):.4f}")
        print("\n   RAZÓN: En grafos bipartitos (8,2)-regulares:")
        print("   - lambda_2 ≈ 3.6-4.0 (segundo eigenvalue)")
        print("   - sqrt(d_avg*(d_avg-1)) ≈ 2.65")
        print("   - lambda_2 / sqrt(d_avg*(d_avg-1)) ≈ 1.37 > 1")
        print("   - Por tanto: 1 - lambda_2/sqrt(...) < 0")
        print("   - Y kappa_Pi = 1/(negativo) < 0")
        print("\n   CONCLUSIÓN: El enfoque de lower bound basado en kappa_Pi")
        print("               NO FUNCIONA para grafos de Tseitin sobre expanders.")
    elif avg_ratio <= 1.0:
        print("\n✅ ¡HÉMOSLO LOGRADO! kappa <= O(1/(sqrt(n) log n))")
        print("   El bound teórico se cumple empíricamente")
    else:
        print(f"\n⚠️  kappa parece ser más grande que el bound teórico")
        print(f"   Factor promedio: {avg_ratio:.2f}× muy grande")

if __name__ == "__main__":
    print("="*70)
    print("VERIFICACIÓN: kappa_Pi <= O(1/(sqrt(n) log n))".center(70))
    print("="*70)
    
    results = verify_kappa_decay(max_n=400, step=30)
    
    if results:
        plot_results(results)
        
        # Mostrar tabla
        print("\n" + "="*70)
        print("RESULTADOS DETALLADOS".center(70))
        print("="*70)
        print(f"{'n':<10} {'kappa_Pi':<15} {'Bound':<15} {'Ratio':<10}")
        print("-"*70)
        
        for n, kappa, bound, ratio in results[:10]:  # Mostrar primeros 10
            print(f"{n:<10} {kappa:<15.6f} {bound:<15.6f} {ratio:<10.4f}")
        
        if len(results) > 10:
            print(f"... y {len(results)-10} más")
    else:
        print("No se pudieron calcular resultados")
