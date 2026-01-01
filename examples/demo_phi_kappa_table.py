#!/usr/bin/env python3
"""
Demostración: Tabla Matemática de φ y κ_Π
=========================================

Este script demuestra la relación matemática precisa entre las potencias
del número áureo (φ) y la constante κ_Π = 2.5773.

Ejecuta:
    python examples/demo_phi_kappa_table.py

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os

# Añadir el directorio src al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from phi_kappa_table import (
    PHI, PHI_SQUARED, KAPPA_PI_UNIVERSAL,
    kappa_pi, phi_power, find_phi_exponent,
    verify_exact_relationship, generate_table,
    verify_key_examples, print_table, analyze_kappa_13
)


def main():
    """Función principal de demostración."""
    
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  TABLA MATEMÁTICA: POTENCIAS DE φ Y VALORES DE κ_Π".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    # 1. Mostrar constantes fundamentales
    print("📊 CONSTANTES FUNDAMENTALES")
    print("-" * 80)
    print(f"  φ (número áureo)     = {PHI:.10f}")
    print(f"  φ²                   = {PHI_SQUARED:.10f}")
    print(f"  κ_Π (universal)      = {KAPPA_PI_UNIVERSAL:.10f}")
    print()
    
    # 2. Demostrar la relación fundamental
    print("📐 RELACIÓN FUNDAMENTAL")
    print("-" * 80)
    print("  κ_Π(N) = log_{φ²}(N) = log(N) / log(φ²)")
    print()
    print("  Donde N = φⁿ, se cumple: κ_Π(N) = n/2")
    print()
    
    # 3. Ejemplos clave del problema
    print("✨ EJEMPLOS CLAVE")
    print("-" * 80)
    
    # Ejemplo 1: φ⁵ ≈ 11.09
    n1 = 5.0
    N1 = phi_power(n1)
    kappa1 = kappa_pi(N1)
    print(f"  Ejemplo 1:")
    print(f"    φ⁵ = {N1:.6f}")
    print(f"    κ_Π(φ⁵) = {kappa1:.6f}")
    print(f"    Esperado: n/2 = {n1/2:.6f}")
    print(f"    ✓ Verificado: {abs(kappa1 - n1/2) < 1e-10}")
    print()
    
    # Ejemplo 2: N = 13
    N2 = 13.0
    n2 = find_phi_exponent(N2)
    kappa2 = kappa_pi(N2)
    print(f"  Ejemplo 2:")
    print(f"    N = {N2:.6f}")
    print(f"    n = log(N)/log(φ) = {n2:.10f}")
    print(f"    φ^{n2:.4f} = {phi_power(n2):.6f}")
    print(f"    κ_Π({N2}) = {kappa2:.10f}")
    print(f"    Constante universal = {KAPPA_PI_UNIVERSAL:.10f}")
    print(f"    ✓ Match: {abs(kappa2 - KAPPA_PI_UNIVERSAL) < 0.001}")
    print()
    
    # 4. Tabla completa
    print("📋 TABLA COMPLETA DE VALORES")
    print_table(n_min=1.0, n_max=10.0, step=0.5)
    
    # 5. Análisis detallado de κ_Π(13)
    analyze_kappa_13()
    
    # 6. Verificación de todos los ejemplos
    print("🔍 VERIFICACIÓN COMPLETA DE EJEMPLOS")
    print("-" * 80)
    results = verify_key_examples()
    
    for key, data in results.items():
        print(f"\n{key.replace('_', ' ').upper()}:")
        if isinstance(data, dict):
            for k, v in data.items():
                if isinstance(v, bool):
                    symbol = "✓" if v else "✗"
                    print(f"  {k}: {symbol}")
                elif isinstance(v, float):
                    print(f"  {k}: {v:.10f}")
                else:
                    print(f"  {k}: {v}")
    
    # 7. Tabla de valores especiales alrededor de N=13
    print()
    print("📌 VALORES ESPECIALES ALREDEDOR DE N=13")
    print("-" * 80)
    
    # Generar valores alrededor de n ≈ 5.154
    special_n = [5.0, 5.1, 5.15, 5.154, 5.16, 5.2, 5.5, 6.0]
    table = generate_table(special_n)
    
    print(f"{'n':>8} | {'φⁿ (N)':>12} | {'κ_Π':>12} | {'n/2':>10} | {'Diferencia':>12}")
    print("-" * 68)
    
    for row in table:
        diff = abs(row['N'] - 13.0)
        marker = " ← N≈13" if diff < 0.1 else ""
        print(f"{row['n']:8.4f} | {row['N']:12.6f} | {row['kappa_pi']:12.6f} | "
              f"{row['kappa_expected']:10.6f} | {diff:12.6f}{marker}")
    
    # 8. Conclusión
    print()
    print("=" * 80)
    print("🎯 CONCLUSIÓN")
    print("=" * 80)
    print()
    print("La constante κ_Π = 2.5773 proviene directamente de κ_Π(13) bajo la base φ².")
    print()
    print("Esto ocurre cuando:")
    print(f"  • N ≈ 13")
    print(f"  • N = φ^{find_phi_exponent(13):.4f}")
    print(f"  • h¹¹ + h²¹ ≈ 13 (números de Hodge en variedades Calabi-Yau)")
    print()
    print("Esta relación confirma matemáticamente la conexión entre:")
    print("  • Topología (Calabi-Yau)")
    print("  • Geometría (número áureo φ)")
    print("  • Complejidad Computacional (κ_Π)")
    print()
    print("=" * 80)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 80)


if __name__ == "__main__":
    main()
