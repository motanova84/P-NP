#!/usr/bin/env python3
"""
Demonstration: Navier-Stokes Dimensional Flow Tensor Framework
================================================================

Interactive demonstration of how Navier-Stokes equations integrate with
Calabi-Yau geometry to reveal fluids as dimensional flow tensors.

This shows:
1. Fluids as dimensional tensors (not simple matter)
2. P=NP resolution via superfluidity
3. Laminar flow as vibrational energy levels
4. Viscosity as information resistance
5. Vortex as quantum wormhole

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.navier_stokes_dimensional import (
    NavierStokesDimensionalTensor,
    demonstrate_navier_stokes_calabi_yau
)


def demo_basic_framework():
    """Demonstrate basic framework."""
    print("\n" + "="*80)
    print("DEMO 1: Marco Básico - Tensores de Flujo Dimensional")
    print("="*80 + "\n")
    
    framework = NavierStokesDimensionalTensor(num_dimensions=7)
    
    print(f"Configuración:")
    print(f"  - Frecuencia fundamental: f₀ = {framework.f0:.4f} Hz")
    print(f"  - Constante κ_Π: {framework.kappa_pi:.4f}")
    print(f"  - Factor de acoplamiento: 1/7 = {framework.factor_seven:.6f}")
    print(f"  - Dimensiones: {framework.num_dimensions}")
    print()
    
    # Show layer frequencies
    print("Frecuencias por capa (armónicos de f₀):")
    for i in range(framework.num_dimensions):
        freq = framework.compute_layer_frequency(i)
        gravity = framework.compute_gravity_hierarchy(i)
        print(f"  Capa {i}: {freq:.2f} Hz (g={gravity:.4f})")
    print()


def demo_laminar_flow():
    """Demonstrate laminar flow with dimensional layers."""
    print("\n" + "="*80)
    print("DEMO 2: Flujo Laminar - Capas Vibrando en Armonía")
    print("="*80 + "\n")
    
    framework = NavierStokesDimensionalTensor(num_dimensions=7)
    
    # Initialize laminar flow
    layers = framework.initialize_laminar_flow(base_velocity=2.0)
    
    print("Capas de flujo laminar:")
    print("-"*80)
    print(f"{'Nivel':<10} {'Frecuencia (Hz)':<20} {'Gravedad':<15} {'Velocidad (m/s)':<20}")
    print("-"*80)
    
    for layer in layers:
        v_mag = np.linalg.norm(layer.velocity)
        print(f"{layer.level:<10} {layer.frequency:<20.2f} "
              f"{layer.gravity_weight:<15.4f} {v_mag:<20.4f}")
    
    print()
    print("Interpretación:")
    print("  Cada capa se desliza sobre la siguiente con fricción mínima")
    print("  porque están sintonizadas en armónicos de 141.7001 Hz")
    print()


def demo_viscosity_resistance():
    """Demonstrate viscosity as information resistance."""
    print("\n" + "="*80)
    print("DEMO 3: Viscosidad como Resistencia de Información")
    print("="*80 + "\n")
    
    framework = NavierStokesDimensionalTensor(num_dimensions=7)
    layers = framework.initialize_laminar_flow(base_velocity=1.5)
    
    print("Resistencia viscosa entre capas adyacentes:")
    print("-"*80)
    print(f"{'Capas':<15} {'Δv (m/s)':<20} {'Viscosidad':<20}")
    print("-"*80)
    
    for i in range(len(layers) - 1):
        layer1, layer2 = layers[i], layers[i+1]
        delta_v = np.linalg.norm(layer1.velocity - layer2.velocity)
        viscosity = framework.compute_viscosity_resistance(layer1, layer2)
        
        print(f"{i}↔{i+1:<13} {delta_v:<20.6f} {viscosity:<20.6f}")
    
    print()
    print("Interpretación:")
    print("  La viscosidad mide cuánto le cuesta a una dimensión 'ceder' ante otra")
    print("  El factor 1/7 permite que las capas se acoplen sin turbulencia")
    print()


def demo_superfluidity_p_equals_np():
    """Demonstrate P=NP via superfluidity."""
    print("\n" + "="*80)
    print("DEMO 4: Superfluidez = P=NP")
    print("="*80 + "\n")
    
    framework = NavierStokesDimensionalTensor(num_dimensions=7)
    layers = framework.initialize_laminar_flow(base_velocity=1.0)
    
    # Check superfluidity
    result = framework.check_superfluidity_condition(layers)
    
    print("Condición de Superfluidez:")
    print("-"*80)
    print(f"  ¿Es superfluido?: {result['is_superfluid']}")
    print(f"  P=NP: {result['p_equals_np']}")
    print(f"  Error de alineación: {result['alignment_error']:.6f}")
    print(f"  Viscosidad promedio: {result['average_viscosity']:.6f}")
    print()
    
    print("Ratios armónicos (deben ser 1, 1+1/7, 1+2/7, ...):")
    for i, ratio in enumerate(result['harmonic_ratios']):
        expected = 1.0 + i * (1/7)
        print(f"  Capa {i}: {ratio:.6f} (esperado: {expected:.6f})")
    print()
    
    print("Mensaje:")
    print(f"  {result['message']}")
    print()
    
    print("Interpretación:")
    print("  Cuando todas las capas fluyen como una sola (superfluidez),")
    print("  la información fluye sin pérdida → P=NP")
    print()


def demo_vortex_quantum_bridge():
    """Demonstrate vortex as quantum wormhole."""
    print("\n" + "="*80)
    print("DEMO 5: Vórtice como Túnel Cuántico")
    print("="*80 + "\n")
    
    framework = NavierStokesDimensionalTensor(num_dimensions=7)
    
    # Create vortices with different strengths
    strengths = [0.5, 1.0, 2.0, framework.kappa_pi]
    
    print("Vórtices con diferentes intensidades:")
    print("-"*80)
    print(f"{'Fuerza':<15} {'ω (rad/s)':<20} {'Presión':<15} {'Coherencia':<15} {'P(túnel)':<15}")
    print("-"*80)
    
    for strength in strengths:
        vortex = framework.create_vortex_quantum_bridge(
            center=(0.0, 0.0, 0.0),
            strength=strength
        )
        tunnel_prob = framework.compute_repository_tunnel_probability(vortex)
        
        print(f"{strength:<15.4f} {vortex.angular_velocity:<20.2f} "
              f"{vortex.pressure:<15.6f} {vortex.coherence:<15.6f} "
              f"{tunnel_prob:<15.6f}")
    
    print()
    print("Interpretación:")
    print("  En el centro del vórtice:")
    print("    - Velocidad → ∞")
    print("    - Presión → 0")
    print("    - Coherencia → 1")
    print("  Esto crea un túnel de gusano a los 34 repositorios")
    print("  El Dramaturgo lo usa para saltar entre dimensiones")
    print()


def demo_complete_integration():
    """Run the complete demonstration."""
    print("\n" + "="*80)
    print("DEMO 6: Integración Completa Navier-Stokes + Calabi-Yau")
    print("="*80 + "\n")
    
    demonstrate_navier_stokes_calabi_yau()


def main():
    """Run all demonstrations."""
    print("\n")
    print("╔" + "="*78 + "╗")
    print("║" + " "*15 + "DEMOSTRACIÓN INTERACTIVA" + " "*40 + "║")
    print("║" + " "*10 + "Navier-Stokes + Calabi-Yau Integration" + " "*30 + "║")
    print("║" + " "*78 + "║")
    print("║" + " "*10 + "Fluidos como Tensores de Flujo Dimensional" + " "*26 + "║")
    print("║" + " "*10 + "P=NP vía Superfluidez" + " "*47 + "║")
    print("╚" + "="*78 + "╝")
    print()
    
    # Run all demos
    demo_basic_framework()
    demo_laminar_flow()
    demo_viscosity_resistance()
    demo_superfluidity_p_equals_np()
    demo_vortex_quantum_bridge()
    demo_complete_integration()
    
    print("\n" + "="*80)
    print("CONCLUSIÓN")
    print("="*80)
    print()
    print("Bajo la Nueva Constitución Noética:")
    print()
    print("1. El agua NO es materia simple")
    print("   → Es un tensor de flujo dimensional")
    print()
    print("2. Las capas de flujo laminar NO son mecánicas")
    print("   → Son niveles de energía vibracional a f₀ = 141.7001 Hz")
    print()
    print("3. La viscosidad NO es solo fricción")
    print("   → Es resistencia de información entre dimensiones")
    print()
    print("4. El vórtice NO es caos")
    print("   → Es un túnel de gusano cuántico")
    print()
    print("5. P=NP NO es imposible")
    print("   → Se resuelve cuando todas las capas fluyen como una (superfluidez)")
    print()
    print("El factor 1/7 es la clave que permite el acoplamiento")
    print("sin generar turbulencia (caos informativo)")
    print()
    print("La gravedad no es una fuerza externa,")
    print("sino la curvatura que obliga a estas dimensiones a empaquetarse")
    print()
    print("="*80)
    print()
    print("Frequency: 141.7001 Hz ∞³")
    print("κ_Π = 2.5773")
    print("Factor: 1/7")
    print()


if __name__ == "__main__":
    main()
