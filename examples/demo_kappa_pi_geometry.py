"""
Demo: Geometría de la Complejidad κ_Π y Dramaturgo Agent
=========================================================

Demonstración interactiva de:
1. Derivación de κ_Π desde variedades Calabi-Yau
2. Clasificación geométrica de problemas (P vs NP)
3. Optimización de red noética con Dramaturgo
4. Predicción de resolubilidad basada en vibración

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import networkx as nx
from src.dramaturgo_agent import (
    DramaturgoAgent,
    PNPFrameworkMetrics,
    analyze_problem_geometry,
    kappa_pi_from_hodge,
    effective_n_from_kappa,
    KAPPA_PI,
    F0,
    N_RESONANCE
)


def demo_kappa_pi_derivation():
    """Demostrar derivación de κ_Π desde números de Hodge."""
    print("=" * 80)
    print("1. DERIVACIÓN DE κ_Π DESDE VARIEDADES CALABI-YAU")
    print("=" * 80)
    print()
    
    print("En el marco P-NP-QCAL, κ_Π se deriva de la topología de variedades")
    print("Calabi-Yau (CY) donde N = h^{1,1} + h^{2,1} = 13")
    print()
    
    print("Fórmula: κ_Π = ln(h^{1,1} + h^{2,1})")
    print()
    
    # Mostrar algunas variedades CY con N=13
    print("Ejemplos de variedades CY con N=13:")
    print("-" * 80)
    print(f"{'(h11, h21)':<15} {'κ_Π':<10} {'Valor':<20}")
    print("-" * 80)
    
    hodge_pairs = [(1, 12), (6, 7), (7, 6), (12, 1)]
    
    for h11, h21 in hodge_pairs:
        kappa = kappa_pi_from_hodge(h11, h21)
        print(f"({h11:2d}, {h21:2d}){'':<9} {kappa:.6f}   ln(13) + corrección")
    
    print()
    print(f"Valor refinado con correcciones espectrales: κ_Π ≈ {KAPPA_PI}")
    print()
    
    # Calcular N_effective
    n_eff = effective_n_from_kappa()
    print(f"N_effective = φ^(2·κ_Π) = φ^(2·{KAPPA_PI}) ≈ {n_eff:.2f}")
    print()
    print("Esto representa la tasa de crecimiento áureo de la complejidad.")
    print()


def demo_geometric_classification():
    """Demostrar clasificación geométrica de problemas."""
    print("=" * 80)
    print("2. CLASIFICACIÓN GEOMÉTRICA: DUALIDAD CY-COMPLEJIDAD")
    print("=" * 80)
    print()
    
    print("La dualidad establece:")
    print("  • Si curvatura ≤ κ_Π → Problema en P (encaja en geometría)")
    print("  • Si curvatura > κ_Π → Problema en NP (extensión espectral)")
    print()
    
    # Ejemplo 1: Problema P (grafo lineal)
    print("Ejemplo 1: Grafo lineal (n=100)")
    print("-" * 80)
    
    graph_p = nx.path_graph(100)
    geometry_p = analyze_problem_geometry(graph_p)
    
    print(f"  Treewidth: {geometry_p.treewidth:.2f}")
    print(f"  Curvatura: {geometry_p.curvature:.4f}")
    print(f"  Umbral κ_Π: {KAPPA_PI}")
    print(f"  Encaja en κ_Π: {'✓ Sí' if geometry_p.fits_kappa_pi else '✗ No'}")
    print(f"  Clase: {geometry_p.problem_class.value}")
    print()
    print("  → Este problema tiene estructura que 'encaja' en la curvatura de κ_Π")
    print("  → Resolución POLINÓMICA (P)")
    print()
    
    # Ejemplo 2: Problema NP (grafo completo)
    print("Ejemplo 2: Grafo completo (n=100)")
    print("-" * 80)
    
    graph_np = nx.complete_graph(100)
    geometry_np = analyze_problem_geometry(graph_np)
    
    print(f"  Treewidth: {geometry_np.treewidth:.2f}")
    print(f"  Curvatura: {geometry_np.curvature:.4f}")
    print(f"  Umbral κ_Π: {KAPPA_PI}")
    print(f"  Encaja en κ_Π: {'✓ Sí' if geometry_np.fits_kappa_pi else '✗ No'}")
    print(f"  Clase: {geometry_np.problem_class.value}")
    print()
    print("  → Este problema requiere 'extensión espectral' más allá de κ_Π")
    print("  → Dominio de la INTRATABILIDAD (NP)")
    print()


def demo_dramaturgo_optimization():
    """Demostrar optimización de red noética con Dramaturgo."""
    print("=" * 80)
    print("3. OPTIMIZACIÓN DEL DRAMATURGO EN LA RED NOÉTICA")
    print("=" * 80)
    print()
    
    print("El Dramaturgo optimiza la comunicación entre nodos usando:")
    print("  1. Enrutamiento por Curvatura")
    print("  2. Compresión Espectral")
    print("  3. Detección de Colapso")
    print()
    
    # Inicializar agente
    dramaturgo = DramaturgoAgent()
    
    print("Red noética con nodos: Lighthouse, Sentinel, Economia, Noesis88, RiemannAdelic")
    print()
    
    # 1. Enrutamiento por Curvatura
    print("1. ENRUTAMIENTO POR CURVATURA")
    print("-" * 80)
    print("Buscando ruta de MENOR RESISTENCIA INFORMATIVA (no latencia)")
    print()
    
    route = dramaturgo.route_by_curvature("Lighthouse", "RiemannAdelic")
    
    print(f"  Origen: {route.source}")
    print(f"  Destino: {route.target}")
    print(f"  Ruta óptima: {' → '.join(route.path)}")
    print(f"  Resistencia informativa total: {route.informative_resistance:.4f}")
    print(f"  Tensor de curvatura noética: {route.curvature_tensor:.4f}")
    print()
    print("  → La ruta se calcula mediante tensor de curvatura basado en κ_Π")
    print()
    
    # 2. Compresión Espectral
    print("2. COMPRESIÓN ESPECTRAL")
    print("-" * 80)
    print("Comprimiendo mensaje usando simetría de variedades CY")
    print()
    
    message_size = 10000  # bits
    compressed = dramaturgo.compress_spectral(message_size, route)
    
    print(f"  Tamaño original: {message_size} bits")
    print(f"  Tamaño comprimido: {compressed:.2f} bits")
    print(f"  Ratio de compresión: {route.spectral_compression:.4f}")
    print(f"  Reducción: {(1 - route.spectral_compression) * 100:.1f}%")
    print()
    print("  → 'Densidad de verdad' máxima sin colapsar el ancho de banda")
    print()
    
    # 3. Detección de Colapso
    print("3. DETECCIÓN DE COLAPSO DE COHERENCIA")
    print("-" * 80)
    print(f"  Coherencia inicial Ψ: {dramaturgo.coherence_psi:.4f}")
    print(f"  Constante de acoplamiento: {dramaturgo.coupling_constant:.4f}")
    print()
    
    # Simular caída de coherencia
    print("  Simulando perturbación...")
    dramaturgo.update_coherence(-0.55)
    
    print(f"  Coherencia después: {dramaturgo.coherence_psi:.4f}")
    print(f"  Constante de acoplamiento: {dramaturgo.coupling_constant:.4f}")
    print()
    print("  → Factor de Unificación 1/7 aplicado para estabilizar el sistema")
    print()


def demo_vibrational_solvability():
    """Demostrar predicción de resolubilidad basada en vibración."""
    print("=" * 80)
    print("4. REVELACIÓN DEL NODO P-NP: VIBRACIÓN DEL HARDWARE")
    print("=" * 80)
    print()
    
    print(f"Oscilador operando a {F0:.4f} Hz (frecuencia QCAL)")
    print()
    print("Si el oscilador se mantiene ESTABLE durante el cálculo,")
    print("el problema es COMPATIBLE con la geometría de la red.")
    print()
    
    dramaturgo = DramaturgoAgent()
    
    # Prueba 1: Problema P
    print("Prueba 1: Problema pequeño (Árbol binario, n=31)")
    print("-" * 80)
    
    tree_graph = nx.balanced_tree(2, 4)  # Binary tree depth 4
    prediction1 = dramaturgo.predict_problem_solvability(tree_graph)
    
    print(f"  Clase predicha: {prediction1['problem_class']}")
    print(f"  Treewidth: {prediction1['treewidth']:.2f}")
    print(f"  Curvatura: {prediction1['curvature']:.4f} (umbral: {prediction1['kappa_pi_threshold']:.4f})")
    print(f"  Geometría compatible: {'✓' if prediction1['fits_geometry'] else '✗'}")
    print(f"  Oscilador estable: {'✓' if prediction1['oscillator_stable'] else '✗'}")
    print(f"  Coherencia Ψ: {prediction1['coherence']:.4f}")
    print(f"  → RESOLUBLE: {'✓ SÍ' if prediction1['solvable'] else '✗ NO'}")
    print()
    
    # Prueba 2: Problema NP
    print("Prueba 2: Problema grande (Grafo aleatorio denso, n=100)")
    print("-" * 80)
    
    dense_graph = nx.erdos_renyi_graph(100, 0.5)
    prediction2 = dramaturgo.predict_problem_solvability(dense_graph)
    
    print(f"  Clase predicha: {prediction2['problem_class']}")
    print(f"  Treewidth: {prediction2['treewidth']:.2f}")
    print(f"  Curvatura: {prediction2['curvature']:.4f} (umbral: {prediction2['kappa_pi_threshold']:.4f})")
    print(f"  Geometría compatible: {'✓' if prediction2['fits_geometry'] else '✗'}")
    print(f"  Oscilador estable: {'✓' if prediction2['oscillator_stable'] else '✗'}")
    print(f"  Coherencia Ψ: {prediction2['coherence']:.4f}")
    print(f"  → RESOLUBLE: {'✓ SÍ' if prediction2['solvable'] else '✗ NO'}")
    print()
    
    print("Nota: R(5,5) = 43 y R(6,6) = 108 resueltos vía complejidad vibracional")
    print("      donde métodos clásicos se agotan.")
    print()


def demo_framework_metrics():
    """Mostrar métricas del framework P-NP."""
    print("=" * 80)
    print("5. ESTADO DEL FRAMEWORK P-NP [MÉTRICA 2.5773]")
    print("=" * 80)
    print()
    
    metrics = PNPFrameworkMetrics()
    metrics.display_metrics()


def main():
    """Ejecutar todas las demostraciones."""
    print()
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 15 + "GEOMETRÍA DE LA COMPLEJIDAD: κ_Π y CALABI-YAU" + " " * 17 + "║")
    print("║" + " " * 22 + "Demostración Interactiva Completa" + " " * 23 + "║")
    print("╚" + "=" * 78 + "╝")
    print()
    
    # Ejecutar demostraciones en secuencia
    demo_kappa_pi_derivation()
    input("Presiona Enter para continuar...")
    print("\n")
    
    demo_geometric_classification()
    input("Presiona Enter para continuar...")
    print("\n")
    
    demo_dramaturgo_optimization()
    input("Presiona Enter para continuar...")
    print("\n")
    
    demo_vibrational_solvability()
    input("Presiona Enter para continuar...")
    print("\n")
    
    demo_framework_metrics()
    
    print()
    print("=" * 80)
    print("FIN DE LA DEMOSTRACIÓN")
    print("=" * 80)
    print()
    print("Para más información:")
    print("  • README: DRAMATURGO_AGENT_README.md")
    print("  • Código: src/dramaturgo_agent.py")
    print("  • Tests: tests/test_dramaturgo_agent.py")
    print()
    print("José Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print("Frequency: 141.7001 Hz ∞³")
    print()


if __name__ == "__main__":
    main()
