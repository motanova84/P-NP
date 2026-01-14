#!/usr/bin/env python3
"""
Demo: LA GRAN TRANSMUTACIÓN

Demostración interactiva del proceso de transmutación P → NP
mediante el diferencial armónico de +10 Hz.

NOESIS ACTIVA RESONANCIA
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from gran_transmutacion import (
    NoesisResonanceEngine,
    demonstrate_transmutation,
    F_P, F_NP, DELTA_F, KAPPA_PI
)


def interactive_demo():
    """Demostración interactiva paso a paso"""
    print("""
┌───────────────────────────────────────────────────────────┐
│                                                           │
│         DEMOSTRACIÓN INTERACTIVA                          │
│         LA GRAN TRANSMUTACIÓN: P-NP + κ_π                │
│                                                           │
└───────────────────────────────────────────────────────────┘
    """)
    
    print("Este demo muestra cómo el diferencial armónico de +10 Hz")
    print("permite la transmutación computacional P → NP.\n")
    
    # Crear motor
    engine = NoesisResonanceEngine()
    
    # Mostrar estado inicial
    print("Estado Inicial:")
    print("─" * 60)
    initial = engine.get_current_state()
    print(initial)
    print()
    
    input("Presiona ENTER para comenzar la transmutación...")
    
    # Ejecutar transmutación
    result = engine.transmute(verbose=True)
    
    # Mostrar trayectoria clave
    print("\n" + "="*60)
    print("TRAYECTORIA DE TRANSMUTACIÓN")
    print("="*60)
    
    key_points = [0, len(result.trajectory)//4, len(result.trajectory)//2, 
                  3*len(result.trajectory)//4, -1]
    
    for i, idx in enumerate(key_points):
        state = result.trajectory[idx]
        print(f"\nPunto {i+1}/5:")
        print(f"  Frecuencia: {state.f_oscillator:.4f} Hz")
        print(f"  κ_π: {state.kappa:.6f}")
        print(f"  Superfluidez: {state.superfluidity:.4f}")
        print(f"  Transmutación: {state.transmutation:.4f}")
    
    return result


def quick_verification():
    """Verificación rápida del mecanismo"""
    print("""
┌───────────────────────────────────────────────────────────┐
│         VERIFICACIÓN RÁPIDA                               │
└───────────────────────────────────────────────────────────┘
    """)
    
    print("Parámetros Fundamentales:")
    print("─" * 40)
    print(f"  P (Lo Construido): {F_P} Hz")
    print(f"  NP (La Expansión): {F_NP} Hz")
    print(f"  Diferencial Armónico: {DELTA_F:.4f} Hz")
    print(f"  κ_π (El Nexo): {KAPPA_PI}")
    print()
    
    print("Ejecutando transmutación...")
    engine = NoesisResonanceEngine()
    result = engine.transmute(verbose=False)
    
    if result.success:
        print("\n✓ TRANSMUTACIÓN EXITOSA")
        print(f"  Estado final: {result.final_state.f_oscillator:.2f} Hz")
        print(f"  Superfluidez: {result.final_state.superfluidity:.4f}")
        print(f"  Coeficiente de transmutación: {result.final_state.transmutation:.4f}")
    else:
        print("\n✗ Transmutación fallida")
        print(f"  Mensaje: {result.message}")
    
    return result


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Demostración de LA GRAN TRANSMUTACIÓN"
    )
    parser.add_argument(
        '--mode',
        choices=['full', 'interactive', 'quick'],
        default='full',
        help='Modo de demostración'
    )
    
    args = parser.parse_args()
    
    if args.mode == 'full':
        demonstrate_transmutation()
    elif args.mode == 'interactive':
        interactive_demo()
    elif args.mode == 'quick':
        quick_verification()
    
    print("\n✧ Fin de la demostración ✧")
    print("QCAL Indexing Active · 141.7001 Hz\n")
