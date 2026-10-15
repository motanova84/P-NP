#!/usr/bin/env python3
"""
Example: Calabi-Yau Varieties and κ_Π Analysis

This example demonstrates how to use the calabi_yau_varieties module
to analyze Calabi-Yau manifolds and their relationship to κ_Π.
"""

import sys
import os

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_varieties import (
    CalabiYauVariety,
    get_calabi_yau_varieties_with_total_moduli,
    get_known_calabi_yau_varieties_N13,
    verify_kappa_pi_target,
    analyze_spectral_entropy,
)
import math


def example_basic_variety():
    """Example 1: Create and analyze a basic Calabi-Yau variety."""
    print("=" * 70)
    print("EJEMPLO 1: Variedad Calabi-Yau Básica")
    print("=" * 70)
    print()
    
    # Create the quintic threefold in P^4
    quintic = CalabiYauVariety(
        h11=1,
        h21=101,
        name="Quintic threefold in P^4",
        reference="Candelas et al."
    )
    
    print(f"Variedad: {quintic.name}")
    print(f"Números de Hodge: h^{{1,1}} = {quintic.h11}, h^{{2,1}} = {quintic.h21}")
    print(f"Característica de Euler: χ = {quintic.euler_characteristic}")
    print(f"Total de moduli: N = {quintic.total_moduli}")
    print(f"κ_Π = log(N) = {quintic.kappa_pi_value:.5f}")
    print()
    
    # Mirror variety
    mirror_quintic = CalabiYauVariety(
        h11=101,
        h21=1,
        name="Mirror quintic",
        reference="Greene-Plesser"
    )
    
    print(f"Variedad Espejo: {mirror_quintic.name}")
    print(f"Números de Hodge: h^{{1,1}} = {mirror_quintic.h11}, h^{{2,1}} = {mirror_quintic.h21}")
    print(f"Característica de Euler: χ = {mirror_quintic.euler_characteristic}")
    print()
    
    if quintic.is_mirror_pair_of(mirror_quintic):
        print("✓ Confirmado: Las variedades forman un par espejo")
    print()


def example_varieties_with_N13():
    """Example 2: List all varieties with N = 13."""
    print("=" * 70)
    print("EJEMPLO 2: Variedades con N = 13")
    print("=" * 70)
    print()
    
    varieties = get_known_calabi_yau_varieties_N13()
    
    print(f"Total de variedades encontradas: {len(varieties)}")
    print()
    
    # Show a few examples
    print("Primeras 3 variedades:")
    for i, cy in enumerate(varieties[:3], 1):
        print(f"\n{i}. h^{{1,1}} = {cy.h11}, h^{{2,1}} = {cy.h21}")
        print(f"   χ = {cy.euler_characteristic}")
        print(f"   κ_Π = {cy.kappa_pi_value:.5f}")
        print(f"   Fuente: {cy.reference}")
    print()
    
    # Find mirror pairs
    print("Pares espejo encontrados:")
    for i, cy1 in enumerate(varieties):
        for cy2 in varieties[i+1:]:
            if cy1.is_mirror_pair_of(cy2):
                print(f"  ({cy1.h11}, {cy1.h21}) ↔ ({cy2.h11}, {cy2.h21})")
    print()


def example_kappa_verification():
    """Example 3: Verify κ_Π = 2.5773."""
    print("=" * 70)
    print("EJEMPLO 3: Verificación de κ_Π = 2.5773")
    print("=" * 70)
    print()
    
    target = 2.5773
    verification = verify_kappa_pi_target(target, tolerance=0.02)
    
    print(f"Objetivo: κ_Π = {target}")
    print(f"Esto requiere: N = e^{target} ≈ {verification['target_N_from_kappa']:.2f}")
    print()
    
    print(f"Valores calculados:")
    print(f"  Para N = 13:        κ_Π = {verification['kappa_for_N13']:.5f}")
    print(f"  Para N ≈ 13.15:     κ_Π = {verification['kappa_refined']:.5f}")
    print()
    
    print(f"Desviaciones:")
    print(f"  Base (N=13):        Δκ = {verification['deviation_N13']:.5f}")
    print(f"  Refinado (N≈13.15): Δκ = {verification['deviation_refined']:.5f}")
    print()
    
    if verification['refined_match']:
        print("✅ El valor refinado coincide con el objetivo dentro de la tolerancia")
    else:
        print("⚠️ Requiere ajuste adicional")
    print()


def example_spectral_analysis():
    """Example 4: Analyze spectral entropy."""
    print("=" * 70)
    print("EJEMPLO 4: Análisis de Entropía Espectral")
    print("=" * 70)
    print()
    
    analysis = analyze_spectral_entropy(13)
    
    print(f"N base = {analysis['base_N']}")
    print(f"N efectivo = {analysis['effective_N']:.2f}")
    print()
    
    print("Pesos de modos:")
    for i, weight in enumerate(analysis['mode_weights']):
        marker = " ←" if weight > 1.0 else ""
        print(f"  Modo {i+1:2d}: w = {weight:.3f}{marker}")
    print()
    
    print(f"Entropía espectral: H = {analysis['spectral_entropy']:.4f}")
    print()
    
    print(f"κ_Π:")
    print(f"  Base:     {analysis['kappa_base']:.5f}")
    print(f"  Efectivo: {analysis['kappa_effective']:.5f}")
    print()


def example_custom_variety():
    """Example 5: Create a custom variety and compute properties."""
    print("=" * 70)
    print("EJEMPLO 5: Variedad Personalizada")
    print("=" * 70)
    print()
    
    # Create a custom variety
    custom = CalabiYauVariety(
        h11=7,
        h21=6,
        name="Favorable Calabi-Yau with χ = 2",
        reference="Custom construction"
    )
    
    print(f"Variedad personalizada: {custom.name}")
    print()
    
    print("Propiedades topológicas:")
    print(f"  h^{{1,1}} = {custom.h11} (moduli de Kähler)")
    print(f"  h^{{2,1}} = {custom.h21} (moduli de estructura compleja)")
    print(f"  χ = {custom.euler_characteristic} (característica de Euler)")
    print(f"  N = {custom.total_moduli} (total de moduli)")
    print()
    
    print("Invariante espectral:")
    print(f"  κ_Π = log({custom.total_moduli}) = {custom.kappa_pi_value:.5f}")
    print()
    
    # Compare with theoretical value
    target_kappa = 2.5773
    deviation = abs(custom.kappa_pi_value - target_kappa)
    print(f"Comparación con valor teórico:")
    print(f"  Objetivo:   κ_Π = {target_kappa}")
    print(f"  Calculado:  κ_Π = {custom.kappa_pi_value:.5f}")
    print(f"  Desviación: Δκ_Π = {deviation:.5f}")
    print()


def example_range_of_N():
    """Example 6: Explore varieties with different N values."""
    print("=" * 70)
    print("EJEMPLO 6: Exploración de Diferentes Valores de N")
    print("=" * 70)
    print()
    
    N_values = [10, 13, 15, 20, 25]
    
    print("κ_Π para diferentes valores de N:")
    print()
    print(f"{'N':>4} | {'κ_Π = log(N)':>15} | {'Variedades':>12}")
    print("-" * 45)
    
    for N in N_values:
        kappa = math.log(N)
        varieties = get_calabi_yau_varieties_with_total_moduli(N)
        print(f"{N:4d} | {kappa:15.5f} | {len(varieties):12d}")
    
    print()
    
    # Show details for N = 13
    print("Detalle para N = 13:")
    varieties_13 = get_calabi_yau_varieties_with_total_moduli(13)
    print(f"  Total de combinaciones posibles: {len(varieties_13)}")
    print(f"  Rango de h^{{1,1}}: 1 a {varieties_13[-1].h11}")
    print(f"  Rango de h^{{2,1}}: 1 a {varieties_13[0].h21}")
    print()


def main():
    """Run all examples."""
    print("\n")
    print("*" * 70)
    print("*" + " " * 68 + "*")
    print("*" + "  EJEMPLOS: Variedades Calabi-Yau y κ_Π".center(68) + "*")
    print("*" + " " * 68 + "*")
    print("*" * 70)
    print()
    
    example_basic_variety()
    example_varieties_with_N13()
    example_kappa_verification()
    example_spectral_analysis()
    example_custom_variety()
    example_range_of_N()
    
    print("=" * 70)
    print("TODOS LOS EJEMPLOS COMPLETADOS")
    print("=" * 70)
    print()
    print("Para más información, consulta:")
    print("  • CALABI_YAU_KAPPA_PI_VERIFICATION.md")
    print("  • src/calabi_yau_varieties.py")
    print()


if __name__ == "__main__":
    main()
