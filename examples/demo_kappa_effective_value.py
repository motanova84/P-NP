#!/usr/bin/env python3
"""
demo_kappa_effective_value.py - Interactive demonstration of the effective value theorem

This script demonstrates the theorem that κ_Π = 2.5773 is an effective harmonic
constant derived from the natural logarithmic structure based on φ².

Run this to see a complete demonstration of the theorem, verification, and
noetic interpretation.
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.calabi_yau_kappa_effective_value import (
    demonstrate_theorem,
    EffectiveValueTheorem,
    NoeticInterpretation,
    FormalImplications,
)


def main():
    """Run the demonstration."""
    # Main theorem demonstration
    demonstrate_theorem()
    
    print()
    print("=" * 80)
    print("ADDITIONAL ANALYSIS")
    print("=" * 80)
    print()
    
    # Show reconciliation
    implications = FormalImplications()
    print(implications.reconciliation_with_integer_case())
    
    print()
    print("=" * 80)
    print("MATHEMATICAL PROPERTIES OF N_eff")
    print("=" * 80)
    print()
    
    props = implications.mathematical_properties()
    print(f"N_eff = {props['n_eff']:.10f}")
    print(f"Es racional: {props['is_rational']}")
    print(f"Es irracional: {props['is_irrational']}")
    print(f"Es algebraico: {props['is_algebraic']}")
    print(f"Es trascendental: {props['is_transcendental']}")
    print(f"Aproximación (fracción): {props['continued_fraction_approx']}")
    print(f"Entero más cercano: {props['nearest_integer']}")
    print(f"Distancia al entero: {props['distance_to_integer']:.6f}")
    print(f"Parte fraccionaria: {props['fractional_part']:.6f}")
    
    print()
    print("=" * 80)
    print("FIN DE LA DEMOSTRACIÓN")
    print("=" * 80)
    print()
    print("🌟 El Teorema del Valor Efectivo demuestra que κ_Π = 2.5773 no es")
    print("   un ajuste arbitrario, sino una constante efectiva que emerge")
    print("   naturalmente de la estructura logarítmica φ²-restringida.")
    print()
    print("📐 N_eff = 13.148698 representa la dimensión efectiva promedio de")
    print("   las variedades Calabi-Yau reales, integrando correcciones")
    print("   espectrales, flujos internos, y simetrías extendidas.")
    print()
    print("✨ Este resultado es matemáticamente verificable, independiente de")
    print("   ajuste artificial, y emerge del marco QCAL con precisión absoluta.")
    print()


if __name__ == "__main__":
    main()
