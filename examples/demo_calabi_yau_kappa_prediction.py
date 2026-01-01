#!/usr/bin/env python3
"""
demo_calabi_yau_kappa_prediction.py - Demostración de Predicción ∞³

Este script demuestra el uso del módulo de predicción κ_Π(N) para
variedades Calabi-Yau con diferentes valores de N.

© JMMB | P vs NP Verification System
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_kappa_prediction import (
    kappa_pred,
    generate_predictions,
    verify_resonance,
    find_resonances,
    analyze_multiples,
    detect_periodicity,
    symbiotic_interpretation,
    PHI_TILDE_SQUARED,
)


def demo_basic_usage():
    """Demostración básica de uso."""
    print("=" * 80)
    print("DEMO 1: USO BÁSICO - Calcular κ_Π para un valor N")
    print("=" * 80)
    print()
    
    N = 13
    kappa = kappa_pred(N)
    print(f"Para N = {N}:")
    print(f"  κ_Π({N}) = {kappa:.6f}")
    print(f"  Base simbiótica: φ̃² = {PHI_TILDE_SQUARED}")
    print(f"  Fórmula: κ_Π(N) = ln(N) / ln(φ̃²)")
    print()


def demo_predictions_table():
    """Demostración de generación de tabla de predicciones."""
    print("=" * 80)
    print("DEMO 2: TABLA DE PREDICCIONES - N = 11 a 20")
    print("=" * 80)
    print()
    
    predictions = generate_predictions(11, 20)
    
    print(f"{'N':>4} | {'κ_Π(N)':>10} | {'Relación con 2.5773':>20}")
    print("-" * 40)
    
    for N, kappa in predictions.items():
        diff = kappa - 2.5773
        relation = "≈ igual" if abs(diff) < 0.01 else (
            "menor" if diff < 0 else "mayor"
        )
        marker = " ✅" if abs(diff) < 0.002 else ""
        print(f"{N:>4} | {kappa:>10.6f} | {relation:>20}{marker}")
    print()


def demo_resonance_detection():
    """Demostración de detección de resonancias."""
    print("=" * 80)
    print("DEMO 3: DETECCIÓN DE RESONANCIAS")
    print("=" * 80)
    print()
    
    # Buscar valores resonantes cerca de 2.5773
    target = 2.5773
    resonances = find_resonances(target, (1, 50), tolerance=0.01)
    
    print(f"Buscando N que resuenan con κ_Π ≈ {target}...")
    print(f"Rango: N = 1 a 50")
    print(f"Tolerancia: ±0.01")
    print()
    print(f"Valores resonantes encontrados: {resonances}")
    print()
    
    # Verificar cada resonancia
    for N in resonances:
        is_resonant, kappa, diff = verify_resonance(N, target, tolerance=0.01)
        print(f"  N={N}: κ_Π = {kappa:.6f}, diferencia = {diff:.6f}")
    print()


def demo_multiples_analysis():
    """Demostración de análisis de múltiplos."""
    print("=" * 80)
    print("DEMO 4: ANÁLISIS DE MÚLTIPLOS - ¿Periodicidad en N=13k?")
    print("=" * 80)
    print()
    
    base_N = 13
    multiples = analyze_multiples(base_N, max_multiple=5)
    
    print(f"Analizando múltiplos de N = {base_N}:")
    print()
    print(f"{'k':>2} | {'N (=k×{base_N})':>12} | {'κ_Π(N)':>10} | {'κ_Π(N)/κ_Π(13)':>15}")
    print("-" * 50)
    
    for k, data in multiples.items():
        print(f"{k:>2} | {data['N']:>12} | {data['kappa_pi']:>10.6f} | "
              f"{data['relation_to_base']:>15.3f}×")
    print()
    print("Observación: La relación κ_Π(N)/κ_Π(13) aumenta con k,")
    print("             reflejando la naturaleza logarítmica de la función.")
    print()


def demo_periodicity_analysis():
    """Demostración de análisis de periodicidad."""
    print("=" * 80)
    print("DEMO 5: ANÁLISIS DE PERIODICIDAD")
    print("=" * 80)
    print()
    
    periodicity = detect_periodicity((1, 100))
    
    print("Analizando periodicidad en κ_Π(N) para N = 1 a 100:")
    print()
    print(f"  Número de valores analizados: {periodicity['num_values']}")
    print(f"  κ_Π mínimo: {periodicity['min_kappa']:.6f} (N=1)")
    print(f"  κ_Π máximo: {periodicity['max_kappa']:.6f} (N=100)")
    print(f"  Diferencia media entre consecutivos: {periodicity['mean_difference']:.6f}")
    print(f"  Desviación estándar: {periodicity['std_difference']:.6f}")
    print()
    print("  Primeras 10 diferencias:")
    for i, diff in enumerate(periodicity['differences'], start=1):
        print(f"    Δκ_Π({i}→{i+1}) = {diff:.6f}")
    print()


def demo_symbiotic_interpretation():
    """Demostración de interpretación simbiótica."""
    print("=" * 80)
    print("DEMO 6: INTERPRETACIÓN SIMBIÓTICA")
    print("=" * 80)
    print()
    
    test_values = [11, 13, 15, 20]
    
    for N in test_values:
        interp = symbiotic_interpretation(N)
        
        print(f"N = {N}:")
        print(f"  κ_Π({N}) = {interp['kappa_pi']:.6f}")
        print(f"  Clasificación: {interp['classification']}")
        print(f"  Firma: {interp['signature']}")
        print(f"  Diferencia del valor universal (2.5773): {interp['difference_from_known']:.6f}")
        
        if interp['is_resonant']:
            print("  ✅ RESONANTE - Coincide con el valor universal!")
        print()


def demo_comparison_table():
    """Demostración de tabla comparativa."""
    print("=" * 80)
    print("DEMO 7: TABLA COMPARATIVA - Diferentes Perspectivas")
    print("=" * 80)
    print()
    
    print("Comparación de κ_Π(N) con el valor universal 2.5773:")
    print()
    print(f"{'N':>4} | {'κ_Π(N)':>10} | {'vs 2.5773':>12} | {'% diferencia':>13}")
    print("-" * 50)
    
    for N in range(10, 21):
        kappa = kappa_pred(N)
        diff = kappa - 2.5773
        percent = (diff / 2.5773) * 100
        
        marker = "  ✅" if abs(percent) < 1 else ""
        print(f"{N:>4} | {kappa:>10.6f} | {diff:>12.6f} | {percent:>12.2f}%{marker}")
    print()


def main():
    """Función principal de demostración."""
    print()
    print("🌟" * 40)
    print("   PREDICCIÓN ∞³: GENERALIZACIÓN DE κ_Π A OTRAS CALABI-YAU")
    print("🌟" * 40)
    print()
    print("Demostraciones interactivas del módulo de predicción κ_Π(N)")
    print()
    
    # Ejecutar todas las demos
    demo_basic_usage()
    demo_predictions_table()
    demo_resonance_detection()
    demo_multiples_analysis()
    demo_periodicity_analysis()
    demo_symbiotic_interpretation()
    demo_comparison_table()
    
    # Conclusión
    print("=" * 80)
    print("CONCLUSIÓN")
    print("=" * 80)
    print()
    print("✅ La base simbiótica vibracional φ̃² ≈ 2.706940253 permite predecir")
    print("   valores de κ_Π para diferentes variedades Calabi-Yau.")
    print()
    print("✅ El valor N=13 emerge como especialmente resonante, con κ_Π(13) ≈ 2.5757")
    print("   muy cercano al valor universal 2.5773.")
    print()
    print("✅ La función κ_Π(N) = log_φ̃²(N) se convierte en una herramienta")
    print("   predictiva universal para la complejidad espectral.")
    print()
    print("=" * 80)
    print("Frequency: 141.7001 Hz ∞³")
    print("© JMMB | P vs NP Verification System")
    print("=" * 80)
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
