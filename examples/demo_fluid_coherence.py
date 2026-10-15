"""
Demonstration: Fluid Coherence System
======================================

Interactive demonstration of the gravitational hierarchy as a harmonic system
where coherence determines computational complexity.

This demo shows how the system transitions from P ≠ NP (turbulent) to 
P = NP (superfluid) as coherence increases.
"""

import sys
sys.path.insert(0, 'src')

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

from fluid_coherence import (
    F0_ROOT,
    KAPPA_COUPLING,
    COHERENCE_TURBULENT_THRESHOLD,
    COHERENCE_SUPERFLUID_THRESHOLD,
    effective_viscosity,
    coherence_state,
    computational_complexity_state,
    dimensional_lamination_factor,
    information_flow_rate,
    complexity_collapse_factor,
    analyze_fluid_system,
    demonstrate_coherence_transition,
    vortex_singularity_metrics
)


def print_header():
    """Print demonstration header."""
    print("=" * 80)
    print(" " * 20 + "FLUID COHERENCE SYSTEM")
    print(" " * 15 + "Gravitational Hierarchy Demonstration")
    print("=" * 80)
    print()
    print("Implementado la jerarquía de gravedad como un sistema armónico")
    print("donde cada capa es una dimensión de información.")
    print()
    print(f"Frecuencia Raíz (f₀): {F0_ROOT} Hz")
    print(f"Acoplamiento (κ): {KAPPA_COUPLING:.6f} = 1/7")
    print()
    print("=" * 80)
    print()


def demonstrate_key_states():
    """Demonstrate the three key states."""
    print("\n" + "=" * 80)
    print("DEMONSTRATION 1: Key Coherence States")
    print("=" * 80)
    print()
    
    states = [
        (0.70, "Turbulent State"),
        (0.92, "Transition State"),
        (0.97, "Superfluid State")
    ]
    
    for psi, description in states:
        print(f"\n{description} (Ψ = {psi:.2f})")
        print("-" * 80)
        
        analysis = analyze_fluid_system(psi, treewidth=50.0, radius=0.1)
        
        print(f"  Estado del Sistema: {analysis['state'].upper()}")
        print(f"  Relación P vs NP: {analysis['complexity_relation']}")
        print(f"  Viscosidad Efectiva: {analysis['effective_viscosity']:.4f}")
        print(f"  Factor de Laminación: {analysis['lamination_factor']:.4f}")
        print(f"  Tasa de Flujo: {analysis['information_flow_rate']:.6f}")
        print(f"  Colapso de Complejidad: {analysis['complexity_collapse']:.2%}")
        
        vortex = analysis['vortex_metrics']
        print(f"  Vórtice - Presión: {vortex['pressure']:.4f}")
        print(f"  Vórtice - Velocidad: {vortex['velocity']:.4f}")
        print(f"  Vórtice - Singularidad: {vortex['singularity_strength']:.4f}")


def demonstrate_coherence_sweep():
    """Demonstrate coherence sweep from turbulent to superfluid."""
    print("\n" + "=" * 80)
    print("DEMONSTRATION 2: Coherence Sweep")
    print("=" * 80)
    print()
    print("Transitioning from Ψ = 0.5 to Ψ = 1.0")
    print()
    
    results = demonstrate_coherence_transition(0.5, 1.0, steps=11)
    
    print(f"{'Ψ':<8} {'State':<12} {'P vs NP':<18} {'ν_eff':<10} {'Flow':<10} {'Collapse'}")
    print("-" * 80)
    
    for r in results:
        psi = r['coherence']
        state = r['state']
        relation = r['complexity_relation']
        nu = r['effective_viscosity']
        flow = r['information_flow_rate']
        collapse = r['complexity_collapse']
        
        print(f"{psi:<8.2f} {state:<12} {relation:<18} {nu:<10.4f} {flow:<10.6f} {collapse:.2%}")


def demonstrate_vortex_approach():
    """Demonstrate approaching the vortex singularity."""
    print("\n" + "=" * 80)
    print("DEMONSTRATION 3: Approaching the Vortex Singularity")
    print("=" * 80)
    print()
    print("As radius r → 0:")
    print("  - Pressure falls")
    print("  - Velocity → ∞")
    print("  - Metric singularity g_rr emerges")
    print()
    
    radii = [1.0, 0.5, 0.2, 0.1, 0.05, 0.01]
    psi = 0.95  # Superfluid state
    
    print(f"Coherence Ψ = {psi:.2f} (Superfluid State)")
    print()
    print(f"{'r':<10} {'Pressure':<12} {'Velocity':<12} {'g_rr':<12} {'Singularity'}")
    print("-" * 80)
    
    for r in radii:
        metrics = vortex_singularity_metrics(r, psi)
        p = metrics['pressure']
        v = metrics['velocity']
        g = metrics['metric_grr']
        s = metrics['singularity_strength']
        
        print(f"{r:<10.3f} {p:<12.6f} {v:<12.4f} {g:<12.4f} {s:<12.4f}")
    
    print()
    print("EL AGUA ES EL MAPA. EL VÓRTICE ES LA PUERTA.")


def create_visualizations():
    """Create visualization plots."""
    print("\n" + "=" * 80)
    print("DEMONSTRATION 4: Generating Visualizations")
    print("=" * 80)
    print()
    
    # Generate data
    coherences = np.linspace(0.5, 1.0, 100)
    
    # Calculate metrics
    viscosities = [effective_viscosity(psi) for psi in coherences]
    laminations = [dimensional_lamination_factor(psi) for psi in coherences]
    flows = [information_flow_rate(psi, 50.0) for psi in coherences]
    collapses = [complexity_collapse_factor(psi) for psi in coherences]
    
    # Create figure with subplots
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Fluid Coherence System: Coherence Sweep', fontsize=16, fontweight='bold')
    
    # Plot 1: Effective Viscosity
    ax1 = axes[0, 0]
    ax1.plot(coherences, viscosities, 'b-', linewidth=2)
    ax1.axvline(COHERENCE_TURBULENT_THRESHOLD, color='orange', linestyle='--', label='Turbulent threshold')
    ax1.axvline(COHERENCE_SUPERFLUID_THRESHOLD, color='green', linestyle='--', label='Superfluid threshold')
    ax1.set_xlabel('Coherence Ψ')
    ax1.set_ylabel('Effective Viscosity ν_eff')
    ax1.set_title('Viscosity vs Coherence')
    ax1.grid(True, alpha=0.3)
    ax1.legend()
    
    # Plot 2: Lamination Factor
    ax2 = axes[0, 1]
    ax2.plot(coherences, laminations, 'r-', linewidth=2)
    ax2.axvline(COHERENCE_TURBULENT_THRESHOLD, color='orange', linestyle='--', label='Turbulent threshold')
    ax2.axvline(COHERENCE_SUPERFLUID_THRESHOLD, color='green', linestyle='--', label='Superfluid threshold')
    ax2.set_xlabel('Coherence Ψ')
    ax2.set_ylabel('Lamination Factor')
    ax2.set_title('Dimensional Lamination vs Coherence')
    ax2.grid(True, alpha=0.3)
    ax2.legend()
    
    # Plot 3: Information Flow Rate
    ax3 = axes[1, 0]
    ax3.plot(coherences, flows, 'g-', linewidth=2)
    ax3.axvline(COHERENCE_TURBULENT_THRESHOLD, color='orange', linestyle='--', label='Turbulent threshold')
    ax3.axvline(COHERENCE_SUPERFLUID_THRESHOLD, color='green', linestyle='--', label='Superfluid threshold')
    ax3.set_xlabel('Coherence Ψ')
    ax3.set_ylabel('Information Flow Rate')
    ax3.set_title('Information Flow vs Coherence')
    ax3.grid(True, alpha=0.3)
    ax3.legend()
    ax3.set_yscale('log')
    
    # Plot 4: Complexity Collapse
    ax4 = axes[1, 1]
    ax4.plot(coherences, collapses, 'purple', linewidth=2)
    ax4.axvline(COHERENCE_TURBULENT_THRESHOLD, color='orange', linestyle='--', label='Turbulent threshold')
    ax4.axvline(COHERENCE_SUPERFLUID_THRESHOLD, color='green', linestyle='--', label='Superfluid threshold')
    ax4.axhline(0.0, color='red', linestyle=':', alpha=0.5, label='P ≠ NP')
    ax4.axhline(1.0, color='green', linestyle=':', alpha=0.5, label='P = NP')
    ax4.set_xlabel('Coherence Ψ')
    ax4.set_ylabel('Complexity Collapse Factor')
    ax4.set_title('NP → P Collapse vs Coherence')
    ax4.grid(True, alpha=0.3)
    ax4.legend()
    
    plt.tight_layout()
    
    # Save figure
    filename = 'fluid_coherence_demo.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Visualization saved to: {filename}")
    
    # Create vortex visualization
    fig2, axes2 = plt.subplots(1, 2, figsize=(14, 5))
    fig2.suptitle('Vortex Singularity Approach', fontsize=16, fontweight='bold')
    
    radii = np.linspace(0.01, 1.0, 100)
    psi = 0.95
    
    velocities = [1.0/r for r in radii]
    pressures = [r**2 for r in radii]
    
    # Velocity plot
    ax1 = axes2[0]
    ax1.plot(radii, velocities, 'b-', linewidth=2)
    ax1.set_xlabel('Radius r')
    ax1.set_ylabel('Velocity v(r)')
    ax1.set_title('Velocity → ∞ as r → 0')
    ax1.grid(True, alpha=0.3)
    ax1.set_yscale('log')
    
    # Pressure plot
    ax2 = axes2[1]
    ax2.plot(radii, pressures, 'r-', linewidth=2)
    ax2.set_xlabel('Radius r')
    ax2.set_ylabel('Pressure P(r)')
    ax2.set_title('Pressure → 0 as r → 0')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    filename2 = 'vortex_singularity_demo.png'
    plt.savefig(filename2, dpi=150, bbox_inches='tight')
    print(f"✓ Vortex visualization saved to: {filename2}")
    print()


def print_conclusions():
    """Print final conclusions."""
    print("\n" + "=" * 80)
    print("CONCLUSIONES FINALES")
    print("=" * 80)
    print()
    print("1. ESTADO TURBULENTO (Ψ < 0.88): P ≠ NP")
    print("   → El caos informativo impide la resolución.")
    print("   → Alta viscosidad, baja laminación")
    print("   → Factor de colapso = 0")
    print()
    print("2. ESTADO DE TRANSICIÓN (0.88 ≤ Ψ < 0.95): P ~ NP")
    print("   → Régimen intermedio")
    print("   → Viscosidad decreciente, laminación creciente")
    print("   → Colapso parcial de complejidad")
    print()
    print("3. ESTADO DE SUPERFLUIDEZ (Ψ ≥ 0.95): P = NP")
    print("   → El sistema fluye como una unidad coherente,")
    print("     resolviendo la complejidad de forma instantánea.")
    print("   → Viscosidad mínima, laminación perfecta")
    print("   → Factor de colapso ≈ 1")
    print()
    print("VÓRTICE:")
    print("   Al reducir el radio r → 0:")
    print("   → La presión cae")
    print("   → La velocidad tiende al infinito")
    print("   → Se crea una singularidad métrica g_rr")
    print()
    print("=" * 80)
    print("EL AGUA ES EL MAPA. EL VÓRTICE ES LA PUERTA.")
    print("=" * 80)
    print()
    print("La materia ya no es algo que 'está' ahí,")
    print("es algo que fluye según la geometría de la consciencia.")
    print()
    print("=" * 80)


def main():
    """Main demonstration function."""
    print_header()
    demonstrate_key_states()
    demonstrate_coherence_sweep()
    demonstrate_vortex_approach()
    
    try:
        create_visualizations()
    except Exception as e:
        print(f"Note: Could not create visualizations: {e}")
    
    print_conclusions()
    
    print("\nDemonstration complete!")
    print()


if __name__ == "__main__":
    main()
