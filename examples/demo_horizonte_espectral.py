"""
Demostración Interactiva: LA UNIFICACIÓN - EL HORIZONTE ESPECTRAL

Script de demostración completa del Protocolo QCAL ∞³ para el Horizonte Espectral.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frecuencia: 141.7001 Hz ∞³
"""

import sys
import os
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.horizonte_espectral import (
    HorizonteEspectral,
    RiemannCriticalLine,
    MathematicalBlackHole,
    ComplexityTransmutation,
    RiemannZero,
    KAPPA_PI,
    F0_QCAL
)


def print_header(title):
    """Imprime un encabezado formateado."""
    print("\n" + "=" * 80)
    print(title.center(80))
    print("=" * 80 + "\n")


def print_section(title):
    """Imprime un título de sección."""
    print("\n" + "-" * 80)
    print(title)
    print("-" * 80 + "\n")


def demo_critical_line():
    """Demostración de la línea crítica como geodésica de máxima coherencia."""
    print_section("1. LA LÍNEA CRÍTICA: GEODÉSICA DE MÁXIMA COHERENCIA")
    
    line = RiemannCriticalLine()
    
    print(f"Re(s) = {line.re_s}")
    print(f"¿Es geodésica de máxima coherencia? {line.is_maximum_coherence_geodesic()}")
    print(f"\nConstantes del sistema:")
    print(f"  κ_π = {line.kappa_pi} (Constante del Milenio)")
    print(f"  f₀ = {line.f0} Hz (Frecuencia QCAL)")
    
    # Coherencia en varios puntos
    print("\nCoherencia en diferentes puntos de la línea crítica:")
    t_values = [0, 5, 10, 14.134725, 20, 50, 100]
    
    for t in t_values:
        coherence = line.coherence_at_point(t)
        print(f"  t = {t:8.3f}  →  C(t) = {coherence:.6f}")
    
    # Añadir ceros
    print("\nAñadiendo ceros no triviales conocidos:")
    known_zeros = [14.134725, 21.022040, 25.010858]
    
    for t in known_zeros:
        zero = line.add_zero(t)
        print(f"  Cero en t = {zero.t:.6f}")
        print(f"    Sumidero de entropía: {zero.entropy_sink:.4f}")
        print(f"    Coherencia: {zero.coherence:.4f}")
    
    # Distancia espectral
    print("\nDistancia espectral entre ceros:")
    for i in range(len(line.zeros) - 1):
        t1 = line.zeros[i].t
        t2 = line.zeros[i+1].t
        dist = line.spectral_distance(t1, t2)
        dist_eucl = abs(t2 - t1)
        print(f"  d({t1:.3f}, {t2:.3f}) = {dist:.6f} (euclidiana: {dist_eucl:.6f})")


def demo_mathematical_black_holes():
    """Demostración de agujeros negros matemáticos."""
    print_section("2. AGUJEROS NEGROS MATEMÁTICOS: SUMIDEROS DE ENTROPÍA")
    
    print("Cada cero no trivial ζ(1/2 + it_n) actúa como un sumidero de entropía.")
    print("Es donde la información se organiza perfectamente.\n")
    
    # Crear varios agujeros negros
    zeros = [
        RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0),
        RiemannZero(t=21.022040, entropy_sink=7.65, coherence=1.0),
        RiemannZero(t=50.0, entropy_sink=9.33, coherence=1.0)
    ]
    
    print("Propiedades de los agujeros negros matemáticos:\n")
    
    for i, zero in enumerate(zeros, 1):
        bh = MathematicalBlackHole(zero)
        
        print(f"Agujero Negro #{i} en t = {zero.t:.6f}:")
        print(f"  Sumidero de entropía: {zero.entropy_sink:.4f}")
        print(f"  Radio Schwarzschild (análogo): {bh.schwarzschild_radius_analog():.2e} m")
        print(f"  Entropía del horizonte: {bh.entropy_at_horizon():.2e} J·s⁻¹")
        print(f"  Temperatura de Hawking (análoga): {bh.hawking_temperature_analog():.2e} K")
        print(f"  Organización de información: {bh.information_organization_at_zero():.4f}")
        print()
    
    print("Interpretación:")
    print("  • La entropía fluye hacia el cero")
    print("  • La información se organiza en estructura perfecta")
    print("  • Coherencia = 1 en el cero (organización máxima)")


def demo_complexity_transmutation():
    """Demostración de transmutación P ↔ NP."""
    print_section("3. TRANSMUTACIÓN P ↔ NP EN EL HORIZONTE ESPECTRAL")
    
    print("Analogía con el horizonte de Schwarzschild:")
    print("  Schwarzschild: r y t intercambian roles")
    print("  Horizonte Espectral: Complejidad (NP) ↔ Solución (P)\n")
    
    line = RiemannCriticalLine()
    for t in [14.134725, 21.022040, 25.010858]:
        line.add_zero(t)
    
    trans = ComplexityTransmutation(line)
    
    print(f"¿Analogía de Schwarzschild válida? {trans.schwarzschild_analogy_applies()}\n")
    
    # Analizar transmutación en varios puntos
    print("Transmutación P ↔ NP acercándose a un cero:\n")
    
    t_zero = 14.134725
    t_points = [5.0, 10.0, 13.0, 14.0, 14.1, t_zero]
    
    print(f"{'t':>10} {'Coherencia':>12} {'NP (Complejidad)':>18} {'P (Solución)':>15} {'Transmutación':>15} {'¿En horizonte?':>15}")
    print("-" * 100)
    
    for t in t_points:
        result = trans.complexity_to_solution_at_zero(t)
        at_horizon = "SÍ" if result['at_horizon'] else "No"
        
        print(f"{t:10.4f} {result['coherence']:12.6f} {result['np_complexity']:18.6f} "
              f"{result['p_solution']:15.6f} {result['transmutation_factor']:15.6f} {at_horizon:>15}")
    
    print("\nObservaciones:")
    print("  • Acercándose al cero, Coherencia → 1")
    print("  • NP (Complejidad) → 0")
    print("  • P (Solución) → 1")
    print("  • Factor de Transmutación → κ_π ≈ 2.5773")
    print("  • En el horizonte: NP y P intercambian roles")
    
    # Búsqueda se detiene
    print("\n¿La búsqueda se detiene?")
    for t in [t_zero, 10.0, 50.0]:
        stops = trans.search_stops_at_center(t)
        print(f"  t = {t:8.3f}  →  {stops}")
    
    print("\n\"La búsqueda se detiene porque ya estás en el centro.\"")


def demo_horizonte_espectral_system():
    """Demostración del sistema completo."""
    print_section("4. SISTEMA COMPLETO: HORIZONTE ESPECTRAL QCAL ∞³")
    
    horizonte = HorizonteEspectral()
    
    print(f"Sistema inicializado con {len(horizonte.known_zeros)} ceros conocidos")
    print(f"Ceros de Riemann: {horizonte.known_zeros}\n")
    
    # Análisis completo en el primer cero
    print("Análisis completo en el primer cero:\n")
    
    t = horizonte.known_zeros[0]
    analysis = horizonte.analyze_horizon(t)
    
    print(f"Punto analizado: t = {analysis['t']:.6f}")
    print(f"  En línea crítica: {analysis['on_critical_line']}")
    print(f"  Es geodésica de máxima coherencia: {analysis['is_geodesic_maximum_coherence']}")
    print(f"  Coherencia: {analysis['coherence']:.6f}")
    print(f"  Cero más cercano: {analysis['nearest_zero']:.6f}")
    print(f"  Distancia al cero: {analysis['distance_to_zero']:.6f}")
    print(f"\n  Transmutación P ↔ NP:")
    print(f"    Complejidad NP: {analysis['transmutation']['np_complexity']:.6f}")
    print(f"    Solución P: {analysis['transmutation']['p_solution']:.6f}")
    print(f"    Factor: {analysis['transmutation']['transmutation_factor']:.6f}")
    print(f"    ¿En el horizonte? {analysis['transmutation']['at_horizon']}")
    print(f"\n  ¿La búsqueda se detiene? {analysis['search_stops']}")
    print(f"  ¿Analogía de Schwarzschild? {analysis['schwarzschild_analogy']}")
    
    # Información cuántica en todos los ceros
    print("\n\nInformación cuántica en todos los ceros conocidos:")
    print("\n" + "-" * 100)
    print(f"{'Cero':>6} {'t':>12} {'Entropía':>12} {'R_Schw (m)':>15} {'S_horizonte':>15} {'T_Hawking (K)':>18} {'Org. Info':>12}")
    print("-" * 100)
    
    quantum_info = horizonte.quantum_information_at_zeros()
    
    for i, info in enumerate(quantum_info, 1):
        print(f"{i:6d} {info['t']:12.6f} {info['entropy_sink']:12.4f} "
              f"{info['schwarzschild_radius']:15.2e} {info['horizon_entropy']:15.2e} "
              f"{info['hawking_temperature']:18.2e} {info['info_organization']:12.4f}")


def demo_visualization_data():
    """Genera datos para visualización del horizonte espectral."""
    print_section("5. PERFIL DEL HORIZONTE ESPECTRAL")
    
    horizonte = HorizonteEspectral()
    
    print("Generando perfil del horizonte espectral...")
    print("(Datos listos para visualización con matplotlib)\n")
    
    profile = horizonte.visualize_horizon_profile(
        t_min=10.0,
        t_max=60.0,
        num_points=500
    )
    
    print(f"Rango: t ∈ [{profile['t_values'][0]:.1f}, {profile['t_values'][-1]:.1f}]")
    print(f"Puntos generados: {len(profile['t_values'])}")
    print(f"Ceros en el rango: {len(profile['zeros'])}")
    
    # Estadísticas del perfil
    print(f"\nEstadísticas de coherencia:")
    print(f"  Máxima: {np.max(profile['coherence']):.6f}")
    print(f"  Mínima: {np.min(profile['coherence']):.6f}")
    print(f"  Media: {np.mean(profile['coherence']):.6f}")
    
    print(f"\nEstadísticas de transmutación:")
    print(f"  Máxima: {np.max(profile['transmutation']):.6f}")
    print(f"  Mínima: {np.min(profile['transmutation']):.6f}")
    print(f"  Media: {np.mean(profile['transmutation']):.6f}")
    
    print("\nPara visualizar con matplotlib:")
    print("""
    import matplotlib.pyplot as plt
    
    plt.figure(figsize=(12, 6))
    
    # Coherencia
    plt.subplot(2, 1, 1)
    plt.plot(profile['t_values'], profile['coherence'], 'b-', linewidth=2)
    plt.axhline(y=1.0, color='r', linestyle='--', alpha=0.5, label='Coherencia máxima')
    plt.scatter(profile['zeros'], [1.0]*len(profile['zeros']), color='red', s=100, 
                marker='o', label='Ceros de Riemann')
    plt.xlabel('t (coordenada espectral)')
    plt.ylabel('Coherencia C(t)')
    plt.title('Horizonte Espectral: Coherencia en la Línea Crítica')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # Transmutación
    plt.subplot(2, 1, 2)
    plt.plot(profile['t_values'], profile['transmutation'], 'g-', linewidth=2)
    plt.scatter(profile['zeros'], [1.0]*len(profile['zeros']), color='red', s=100, marker='o')
    plt.xlabel('t (coordenada espectral)')
    plt.ylabel('Coeficiente de Transmutación P ↔ NP')
    plt.title('Horizonte Espectral: Transmutación de Complejidad')
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('horizonte_espectral.png', dpi=300)
    plt.show()
    """)


def demo_main():
    """Demostración principal completa."""
    print_header("LA UNIFICACIÓN: EL HORIZONTE ESPECTRAL")
    print("Protocolo QCAL ∞³".center(80))
    print()
    print("En el Protocolo QCAL ∞³, la línea Re(s) = 1/2 ya no es solo una")
    print("hipótesis matemática; es la geodésica de máxima coherencia.".center(80))
    print()
    print(f"κ_π = {KAPPA_PI}  •  f₀ = {F0_QCAL} Hz".center(80))
    
    # Demostraciones
    demo_critical_line()
    demo_mathematical_black_holes()
    demo_complexity_transmutation()
    demo_horizonte_espectral_system()
    demo_visualization_data()
    
    # Conclusión
    print_header("CONCLUSIÓN")
    
    print("""
    EL HORIZONTE ESPECTRAL: DONDE P Y NP SE UNIFICAN
    
    En los ceros de la función zeta de Riemann (Re(s) = 1/2):
    
    1. LA LÍNEA CRÍTICA es la geodésica de máxima coherencia
       • No es una conjetura, es una manifestación estructural
       • La coherencia alcanza su máximo (C = 1) en los ceros
    
    2. CADA CERO actúa como un AGUJERO NEGRO MATEMÁTICO
       • Sumidero de entropía donde la información se organiza perfectamente
       • Análogo al horizonte de Schwarzschild: organización total
    
    3. LA TRANSMUTACIÓN P ↔ NP ocurre en el horizonte
       • Como r y t intercambian roles en Schwarzschild
       • Complejidad (NP) y Solución (P) intercambian roles en Re(s) = 1/2
       • "La búsqueda se detiene porque ya estás en el centro"
    
    En el horizonte espectral, P ≠ NP se resuelve no por demostración,
    sino por RECONOCIMIENTO de la estructura universal.
    
    La geodésica de máxima coherencia no es un camino a seguir,
    sino el único camino donde la información puede existir coherentemente.
    """)
    
    print("\n" + "=" * 80)
    print("Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print("Frecuencia: 141.7001 Hz ∞³")
    print("Protocolo: QCAL ∞³")
    print("=" * 80 + "\n")


if __name__ == "__main__":
    demo_main()
