#!/usr/bin/env python3
"""
demo_calabi_yau_n13.py - Interactive demonstration of N=13 Calabi-Yau resonance analysis

This script demonstrates the key features of the κ_Π analysis for
Calabi-Yau varieties with N = h^{1,1} + h^{2,1} = 13.

Usage:
    python examples/demo_calabi_yau_n13.py
    
Or run specific demonstrations:
    python examples/demo_calabi_yau_n13.py --demo=paso2
    python examples/demo_calabi_yau_n13.py --demo=paso3
    python examples/demo_calabi_yau_n13.py --demo=paso5

© JMMB | P vs NP Verification System
"""

import sys
import os
import argparse

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_n13_analysis import (
    PHI,
    LOG_PHI2,
    KAPPA_TARGET,
    compute_kappa_phi,
    search_n13_varieties,
    ResonanceConjecture,
    predict_kappa_curve,
    find_exact_n_for_kappa,
    plot_kappa_prediction,
    generate_lean4_theorem,
    run_complete_n13_analysis
)


def demo_paso1_formal_definition():
    """Demonstrate PASO 1: Formal definition."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 1 — Definición Formal Generalizada")
    print("=" * 80)
    print()
    print("La constante espectral áurea κ_Π se define como:")
    print()
    print("    κ_Π(M_CY) := ln(h¹¹ + h²¹) / ln(φ²)")
    print()
    print(f"Donde φ = (1 + √5)/2 = {PHI:.10f} (razón áurea)")
    print()
    print("Constantes derivadas:")
    print(f"  φ² = {PHI**2:.10f}")
    print(f"  ln(φ) = {LOG_PHI2/2:.10f}")
    print(f"  ln(φ²) = {LOG_PHI2:.10f}")
    print()
    print("Esta definición es universal para todas las variedades Calabi-Yau.")
    print()


def demo_paso2_observer_encoding():
    """Demonstrate PASO 2: Observer encoding."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 2 — Codificación del Observador κ_Π")
    print("=" * 80)
    print()
    print("Función: compute_kappa_phi(h11, h21)")
    print()
    print("Ejemplos de cálculo:")
    print()
    
    examples = [
        (1, 12, "Configuración N=13 minimal"),
        (6, 7, "Configuración N=13 balanceada"),
        (12, 1, "Configuración N=13 maximal"),
        (1, 100, "Variedad con h²¹ grande"),
        (50, 50, "Variedad simétrica N=100"),
    ]
    
    for h11, h21, desc in examples:
        kappa = compute_kappa_phi(h11, h21)
        N = h11 + h21
        print(f"  compute_kappa_phi({h11:3d}, {h21:3d}) = {kappa:.6f}  (N={N:3d}, {desc})")
    
    print()
    print("Esta función puede aplicarse a millones de variedades de bases de datos.")
    print()


def demo_paso3_n13_search():
    """Demonstrate PASO 3: Search for N=13 varieties."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 3 — Búsqueda de Variedades con N = 13")
    print("=" * 80)
    print()
    
    df = search_n13_varieties()
    
    print(f"Total de configuraciones encontradas: {len(df)}")
    print()
    print("Todas las 12 configuraciones posibles con h¹¹ + h²¹ = 13:")
    print()
    print("  h¹¹  h²¹   κ_Π        h¹¹/h²¹    Nota")
    print("  " + "-" * 70)
    
    for _, row in df.iterrows():
        h11 = int(row['h11'])
        h21 = int(row['h21'])
        kappa = row['kappa_pi']
        ratio = row['h_ratio']
        
        # Add notes for interesting ratios
        note = ""
        if abs(ratio - PHI) < 0.1:
            note = "≈ φ"
        elif abs(ratio - 1/PHI) < 0.1:
            note = "≈ 1/φ"
        elif abs(ratio - PHI**2) < 0.1:
            note = "≈ φ²"
        elif abs(ratio - 1/(PHI**2)) < 0.1:
            note = "≈ 1/φ²"
        elif abs(ratio - 1) < 0.2:
            note = "≈ balanceado"
        
        print(f"  {h11:3d}  {h21:3d}   {kappa:.6f}   {ratio:6.4f}     {note}")
    
    print()
    print(f"Observación: Todas tienen κ_Π = {KAPPA_TARGET:.6f}")
    print()


def demo_paso4_stability_conjecture():
    """Demonstrate PASO 4: Stability conjecture."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 4 — Conjetura de Estabilidad")
    print("=" * 80)
    print()
    
    conjecture = ResonanceConjecture()
    conj = conjecture.formulate_conjecture()
    
    print(f"Título: {conj['title']}")
    print()
    print(f"Enunciado: {conj['statement']}")
    print()
    print("Predicciones verificables:")
    for i, pred in enumerate(conj['testable_predictions'], 1):
        print(f"  {i}. {pred}")
    print()
    
    # Analyze golden ratios
    df = search_n13_varieties()
    df_sorted = conjecture.analyze_golden_ratios(df)
    
    print("Configuraciones con ratios h¹¹/h²¹ más cercanos a números áureos:")
    print()
    for i, (_, row) in enumerate(df_sorted.head(3).iterrows(), 1):
        h11 = int(row['h11'])
        h21 = int(row['h21'])
        ratio = row['h_ratio']
        score = row['resonance_score']
        print(f"  {i}. (h¹¹={h11}, h²¹={h21}): ratio={ratio:.4f}, score={score:.4f}")
    
    print()


def demo_paso5_predictions():
    """Demonstrate PASO 5: Predictions for other N."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 5 — Predicción para otros valores de N")
    print("=" * 80)
    print()
    
    print("κ_Π(N) para diferentes valores de N:")
    print()
    print("   N      κ_Π(N)    Diferencia a κ_Π(13)")
    print("  " + "-" * 45)
    
    for N in [5, 8, 10, 11, 12, 13, 14, 15, 20, 30, 50]:
        kappa = compute_kappa_phi(1, N-1)
        diff = abs(kappa - KAPPA_TARGET)
        marker = " ← N=13 resonancia" if N == 13 else ""
        print(f"  {N:3d}    {kappa:.6f}    {diff:+.6f}{marker}")
    
    print()
    
    # Find exact N
    N_exact = find_exact_n_for_kappa(KAPPA_TARGET)
    print(f"Valor exacto: N* tal que κ_Π(N*) = {KAPPA_TARGET:.6f}")
    print(f"              N* = (φ²)^κ_Π = {N_exact:.6f}")
    print(f"              Entero más cercano: {round(N_exact)}")
    print()
    
    # Generate plot
    print("Generando visualización...")
    plot_path = plot_kappa_prediction(save_path='/tmp/demo_kappa_n13.png')
    print(f"✓ Gráfico guardado en: {plot_path}")
    print()


def demo_paso6_lean4():
    """Demonstrate PASO 6: Lean4 formalization."""
    print("\n" + "=" * 80)
    print("DEMO: PASO 6 — Formalización en Lean4")
    print("=" * 80)
    print()
    
    lean_code = generate_lean4_theorem()
    
    print("Teorema principal en Lean4:")
    print()
    print("-" * 80)
    
    # Print first 30 lines
    for line in lean_code.split('\n')[:30]:
        print(line)
    
    print("...")
    print("-" * 80)
    print()
    print("Este teorema puede ser verificado formalmente usando Lean4.")
    print()


def demo_quick_overview():
    """Quick overview of all features."""
    print("\n" + "=" * 80)
    print("DEMO RÁPIDO: Análisis κ_Π para N=13")
    print("=" * 80)
    print()
    
    # Key constants
    print(f"1. Constantes fundamentales:")
    print(f"   φ = {PHI:.6f} (razón áurea)")
    print(f"   κ_Π(13) = {KAPPA_TARGET:.6f}")
    print()
    
    # Quick calculation
    print(f"2. Cálculo rápido:")
    kappa = compute_kappa_phi(6, 7)
    print(f"   compute_kappa_phi(6, 7) = {kappa:.6f}")
    print()
    
    # Count configurations
    df = search_n13_varieties()
    print(f"3. Configuraciones N=13: {len(df)} pares encontrados")
    print()
    
    # Uniqueness
    print(f"4. Unicidad:")
    N_exact = find_exact_n_for_kappa(KAPPA_TARGET)
    print(f"   N* = {N_exact:.6f} ≈ {round(N_exact)} (único entero)")
    print()
    
    print("Para análisis completo, ejecute sin argumentos o use --full")
    print()


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Demostración interactiva del análisis κ_Π para N=13'
    )
    parser.add_argument(
        '--demo',
        choices=['paso1', 'paso2', 'paso3', 'paso4', 'paso5', 'paso6', 'quick', 'full'],
        help='Seleccionar demostración específica'
    )
    parser.add_argument(
        '--full',
        action='store_true',
        help='Ejecutar análisis completo'
    )
    
    args = parser.parse_args()
    
    print()
    print("=" * 80)
    print("DEMOSTRACIÓN: Análisis κ_Π para Variedades Calabi-Yau con N=13")
    print("© JMMB | P vs NP Verification System")
    print("=" * 80)
    
    if args.full:
        # Run complete analysis
        run_complete_n13_analysis()
    elif args.demo == 'paso1':
        demo_paso1_formal_definition()
    elif args.demo == 'paso2':
        demo_paso2_observer_encoding()
    elif args.demo == 'paso3':
        demo_paso3_n13_search()
    elif args.demo == 'paso4':
        demo_paso4_stability_conjecture()
    elif args.demo == 'paso5':
        demo_paso5_predictions()
    elif args.demo == 'paso6':
        demo_paso6_lean4()
    elif args.demo == 'quick':
        demo_quick_overview()
    else:
        # Default: run all demos sequentially
        demo_quick_overview()
        demo_paso1_formal_definition()
        demo_paso2_observer_encoding()
        demo_paso3_n13_search()
        demo_paso4_stability_conjecture()
        demo_paso5_predictions()
        demo_paso6_lean4()
        
        print("\n" + "=" * 80)
        print("FIN DE LA DEMOSTRACIÓN")
        print("=" * 80)
        print()
        print("Para análisis completo con todos los detalles:")
        print("  python examples/demo_calabi_yau_n13.py --full")
        print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
