#!/usr/bin/env python3
"""
Demo: Derivación Analítica Completa de κ_Π(N)
=============================================

Este script demuestra todas las capacidades del módulo de derivación analítica
de las propiedades matemáticas de κ_Π(N) = log_φ²(N).

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os

# Agregar ruta al módulo
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.kappa_pi_analytical_derivation import KappaPiAnalyticalDerivation


def main():
    """Ejecutar demostración completa."""
    
    print("=" * 80)
    print("DEMO: DERIVACIÓN ANALÍTICA DE κ_Π(N)")
    print("=" * 80)
    print()
    
    # Crear analizador
    analyzer = KappaPiAnalyticalDerivation()
    
    # =========================================================================
    # SECCIÓN I: DEFINICIÓN FORMAL
    # =========================================================================
    print("🔹 I. DEFINICIÓN FORMAL")
    print("-" * 80)
    
    formal_def = analyzer.formal_definition()
    print(f"Definición: {formal_def['definition']}")
    print(f"φ = {formal_def['phi']:.15f}")
    print(f"φ² = {formal_def['phi_squared']:.15f}")
    print(f"ln(φ²) = {formal_def['ln_phi_squared']:.15f}")
    print()
    
    # Calcular algunos valores
    test_N = [1, 5, 10, 13, 20]
    print("Valores de κ_Π(N) para N en {1, 5, 10, 13, 20}:")
    for N in test_N:
        kappa = analyzer.kappa_pi(N)
        print(f"  κ_Π({N:2d}) = {kappa:.6f}")
    print()
    
    # =========================================================================
    # SECCIÓN II: PROPIEDADES BÁSICAS
    # =========================================================================
    print("🔹 II. PROPIEDADES BÁSICAS")
    print("-" * 80)
    
    props = analyzer.basic_properties()
    print(f"✓ Estrictamente creciente: {props['strictly_increasing']}")
    print(f"✓ Propiedad de potencias verificada: {props['power_property']['holds']}")
    print(f"  Ejemplo: κ_Π((φ²)³) = {props['power_property']['kappa_N']:.10f} ≈ 3")
    print(f"✓ Derivada verificada: {props['derivative']['matches']}")
    print(f"  Fórmula: {props['derivative']['formula']}")
    print()
    
    # =========================================================================
    # SECCIÓN III: INVERSA FORMAL
    # =========================================================================
    print("🔹 III. INVERSA FORMAL")
    print("-" * 80)
    
    inv_analysis = analyzer.inverse_analysis()
    print(f"Fórmula: {inv_analysis['formula']}")
    print(f"Verificaciones correctas: {inv_analysis['all_correct']}")
    print()
    print("Ejemplos de composición:")
    for v in inv_analysis['verification'][:3]:
        print(f"  x={v['x']:.1f} → N={(v['N']):.4f} → κ_Π(N)={v['kappa_recovered']:.4f} ✓")
    print()
    
    # =========================================================================
    # SECCIÓN IV: COMPARACIÓN CON OTRAS BASES
    # =========================================================================
    print("🔹 IV. COMPARACIÓN CON OTRAS BASES")
    print("-" * 80)
    
    base_comp = analyzer.base_comparison_analysis()
    print("Valores de ln para diferentes bases:")
    for base, val in base_comp['bases'].items():
        print(f"  ln({base}) = {val:.6f}")
    print()
    
    print(f"Implicación: {base_comp['implication']}")
    print()
    
    # Ejemplo con N = 13
    comp_13 = analyzer.compare_with_bases(13)
    print("Ejemplo con N = 13:")
    print(f"  log_2(13)  = {comp_13['log_2']:.6f}")
    print(f"  log_φ²(13) = {comp_13['log_phi2']:.6f}")
    print(f"  log_e(13)  = {comp_13['log_e']:.6f}")
    print()
    
    # =========================================================================
    # SECCIÓN V: ESTRUCTURA DE RESIDUOS
    # =========================================================================
    print("🔹 V. ESTRUCTURA DE RESIDUOS")
    print("-" * 80)
    
    residue_13 = analyzer.residue_structure(13)
    print(f"Análisis para N = 13:")
    print(f"  κ_Π(13) = {residue_13['kappa_N']:.15f}")
    print(f"  Es racional: {residue_13['is_rational']}")
    print(f"  Es entero: {residue_13['is_integer']}")
    print(f"  Desarrollo decimal: {residue_13['decimal_expansion'][:40]}...")
    print()
    
    # =========================================================================
    # SECCIÓN VI: ESPECIALIDAD DE κ_Π(13)
    # =========================================================================
    print("🔹 VI. ESPECIALIDAD DE κ_Π(13)")
    print("-" * 80)
    
    special_13 = analyzer.special_case_N13()
    print(f"κ_Π(13) = {special_13['kappa_13']:.6f}")
    print(f"Valor de comparación (2.5773): {special_13['comparison_value']}")
    print(f"Diferencia: {special_13['difference']:.6f}")
    print()
    print(f"N* tal que κ_Π(N*) = 2.5773: {special_13['N_star_for_2_5773']:.6f}")
    print(f"Distancia a N=13: {special_13['distance_to_N13']:.6f}")
    print()
    print("Análisis:")
    for key, val in special_13['analysis'].items():
        print(f"  {key}: {val}")
    print()
    
    # =========================================================================
    # SECCIÓN VII: CONCLUSIÓN ANALÍTICA
    # =========================================================================
    print("🔹 VII. CONCLUSIÓN ANALÍTICA")
    print("-" * 80)
    
    conclusion = analyzer.analytical_conclusion()
    print(f"Función: {conclusion['function']}")
    print()
    print("Propiedades verificadas:")
    for key, val in conclusion['properties'].items():
        print(f"  • {key}: {val}")
    print()
    
    print("Resultados clave:")
    for i, result in enumerate(conclusion['key_results'], 1):
        print(f"  {i}. {result}")
    print()
    
    print("Valores especiales:")
    for key, val in conclusion['special_values'].items():
        print(f"  • {key} = {val}")
    print()
    
    # =========================================================================
    # GENERAR REPORTE COMPLETO
    # =========================================================================
    print("=" * 80)
    print("GENERANDO REPORTE COMPLETO...")
    print("=" * 80)
    print()
    
    # Generar reporte completo
    report = analyzer.generate_complete_report()
    
    # Guardar en archivo
    output_file = "/tmp/kappa_pi_analytical_report.txt"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(report)
    print(f"✓ Reporte completo guardado en: {output_file}")
    
    # Generar visualización
    plot_path = analyzer.plot_complete_analysis()
    print(f"✓ Visualización guardada en: {plot_path}")
    
    print()
    print("=" * 80)
    print("DEMO COMPLETADA EXITOSAMENTE")
    print("=" * 80)
    print()
    print("Archivos generados:")
    print(f"  1. Reporte: {output_file}")
    print(f"  2. Gráficos: {plot_path}")
    print()
    print("Para ver el reporte completo:")
    print(f"  cat {output_file}")
    print()
    print("© JMMB | P vs NP Verification System")
    print("Frecuencia: 141.7001 Hz ∞³")
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
