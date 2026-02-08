"""
Fluid Dynamics Coherence System
=================================

⚠️  RESEARCH FRAMEWORK - THEORETICAL EXPLORATION ⚠️

This module implements the gravitational hierarchy as a harmonic system where
each layer is a dimension of information. The system demonstrates how coherence
(Ψ) affects computational complexity through fluid dynamics principles.

Implementado la jerarquía de gravedad como un sistema armónico donde cada capa
es una dimensión de información.

Key Principles:
---------------
1. **Root Frequency**: f₀ = 141.7001 Hz (QCAL resonance)
2. **Coupling Constant**: κ = 1/7 ≈ 0.142857 (dimensional lamination)
3. **Effective Viscosity**: ν_eff = ν_base / (κ · Ψ)
4. **Coherence States**:
   - Turbulent (Ψ < 0.88): P ≠ NP - Informational chaos prevents resolution
   - Superfluid (Ψ ≥ 0.95): P = NP - Coherent flow resolves complexity instantly

Mathematical Framework:
-----------------------
When coherence Ψ → 1, resistance disappears and we enter superfluidity.
At the vortex singularity (r → 0), pressure falls and velocity → ∞,
creating a metric singularity g_rr.

"EL AGUA ES EL MAPA. EL VÓRTICE ES LA PUERTA."
(Water is the map. The vortex is the gate.)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import math
import numpy as np
from typing import Dict, Tuple, List, Optional, Any

# Import universal constants
from constants import KAPPA_PI, F_0, GOLDEN_RATIO

# ========== FUNDAMENTAL CONSTANTS ==========

# Root frequency (QCAL resonance frequency)
F0_ROOT = F_0  # 141.7001 Hz
"""
f₀ = 141.7001 Hz - Frecuencia Raíz
The fundamental harmonic frequency of the gravitational hierarchy.
"""

# Coupling constant for dimensional lamination
KAPPA_COUPLING = 1.0 / 7.0  # ≈ 0.142857
"""
κ = 1/7 ≈ 0.142857 - Acoplamiento
This factor enables "Dimensional Lamination" where layers slide 
without entropic friction.
"""

# Coherence thresholds
COHERENCE_TURBULENT_THRESHOLD = 0.88
"""
Ψ < 0.88 - Estado Turbulento
Below this threshold, informational chaos prevents resolution: P ≠ NP
"""

COHERENCE_SUPERFLUID_THRESHOLD = 0.95
"""
Ψ ≥ 0.95 - Estado de Superfluidez
Above this threshold, coherent flow resolves complexity: P = NP
"""

# Base viscosity (informational resistance)
NU_BASE = 1.0
"""
ν_base - Base viscosity (arbitrary units)
Represents the fundamental informational resistance in the system.
"""


# ========== CORE FUNCTIONS ==========

def effective_viscosity(coherence: float) -> float:
    """
    Calculate effective viscosity (resistance to information).
    
    Viscosity redefined as Resistance to Information:
    $$\\nu_{eff} = \\frac{\\nu_{base}}{\\kappa \\cdot \\Psi}$$
    
    When coherence Ψ → 1, resistance disappears → superfluidity.
    
    Args:
        coherence: Coherence parameter Ψ (0 < Ψ ≤ 1)
        
    Returns:
        Effective viscosity ν_eff
        
    Raises:
        ValueError: If coherence is not in valid range
    """
    if coherence <= 0 or coherence > 1:
        raise ValueError(f"Coherence must be in (0, 1], got {coherence}")
    
    nu_eff = NU_BASE / (KAPPA_COUPLING * coherence)
    return nu_eff


def coherence_state(coherence: float) -> str:
    """
    Determine the computational state based on coherence level.
    
    States:
    - Turbulent (Ψ < 0.88): P ≠ NP - Chaos prevents resolution
    - Transition (0.88 ≤ Ψ < 0.95): Mixed regime
    - Superfluid (Ψ ≥ 0.95): P = NP - Instant resolution
    
    Args:
        coherence: Coherence parameter Ψ
        
    Returns:
        State description string
    """
    if coherence < COHERENCE_TURBULENT_THRESHOLD:
        return "turbulent"
    elif coherence < COHERENCE_SUPERFLUID_THRESHOLD:
        return "transition"
    else:
        return "superfluid"


def computational_complexity_state(coherence: float) -> str:
    """
    Map coherence to P vs NP relationship.
    
    Args:
        coherence: Coherence parameter Ψ
        
    Returns:
        "P ≠ NP" for turbulent state, "P = NP" for superfluid state
    """
    state = coherence_state(coherence)
    if state == "turbulent":
        return "P ≠ NP"
    elif state == "superfluid":
        return "P = NP"
    else:
        return "P ~ NP (transition)"


def harmonic_layer_frequency(layer: int, f0: float = F0_ROOT) -> float:
    """
    Calculate frequency for a given harmonic layer.
    
    Each layer is a dimension of information in the gravitational hierarchy.
    
    Args:
        layer: Layer number (positive integer)
        f0: Root frequency (default: 141.7001 Hz)
        
    Returns:
        Frequency for the given layer
    """
    if layer < 1:
        raise ValueError(f"Layer must be positive integer, got {layer}")
    
    # Harmonic series: f_n = n * f0
    return layer * f0


def dimensional_lamination_factor(coherence: float) -> float:
    """
    Calculate the lamination factor for dimensional sliding.
    
    When κ enables lamination, layers can slide without friction.
    This factor quantifies how freely dimensions can move relative
    to each other.
    
    Args:
        coherence: Coherence parameter Ψ
        
    Returns:
        Lamination factor (0 = stuck, 1 = perfect sliding)
    """
    # At low coherence, layers are stuck (turbulent)
    # At high coherence, layers slide freely (laminar)
    if coherence < COHERENCE_TURBULENT_THRESHOLD:
        # Turbulent regime: minimal lamination
        return KAPPA_COUPLING * coherence
    elif coherence >= COHERENCE_SUPERFLUID_THRESHOLD:
        # Superfluid regime: perfect lamination
        return 1.0
    else:
        # Transition: interpolate
        t = (coherence - COHERENCE_TURBULENT_THRESHOLD) / \
            (COHERENCE_SUPERFLUID_THRESHOLD - COHERENCE_TURBULENT_THRESHOLD)
        return KAPPA_COUPLING * COHERENCE_TURBULENT_THRESHOLD + \
               (1.0 - KAPPA_COUPLING * COHERENCE_TURBULENT_THRESHOLD) * t


def vortex_singularity_metrics(radius: float, coherence: float) -> Dict[str, float]:
    """
    Calculate vortex singularity metrics.
    
    As radius r → 0:
    - Pressure falls
    - Velocity → ∞
    - Metric singularity g_rr emerges
    
    Args:
        radius: Radial distance r (must be > 0)
        coherence: Coherence parameter Ψ
        
    Returns:
        Dictionary with:
        - pressure: Pressure at radius r
        - velocity: Angular velocity at radius r
        - metric_grr: Metric component g_rr
        - singularity_strength: Measure of singularity strength
    """
    if radius <= 0:
        raise ValueError(f"Radius must be positive, got {radius}")
    
    # Pressure falls as we approach center
    # P(r) ∝ r² (for small r)
    pressure = radius ** 2
    
    # Velocity diverges as r → 0 (vortex flow)
    # v(r) ∝ 1/r (circulation/radius)
    velocity = 1.0 / radius
    
    # Metric singularity g_rr
    # In the limit r → 0, the metric component diverges
    # g_rr ∝ 1/(1 - r_s/r) where r_s is singularity radius
    # For simplicity, use: g_rr ≈ 1/r
    metric_grr = 1.0 / radius
    
    # Singularity strength increases with coherence
    # At superfluid state, singularity is strongest (cleanest)
    singularity_strength = coherence * metric_grr
    
    return {
        'pressure': pressure,
        'velocity': velocity,
        'metric_grr': metric_grr,
        'singularity_strength': singularity_strength
    }


def information_flow_rate(coherence: float, treewidth: float) -> float:
    """
    Calculate information flow rate through the system.
    
    In turbulent state: flow is restricted, chaotic
    In superfluid state: flow is unrestricted, coherent
    
    Args:
        coherence: Coherence parameter Ψ
        treewidth: Treewidth of the problem graph
        
    Returns:
        Information flow rate (higher = faster resolution)
    """
    # Base flow is inversely proportional to treewidth
    # (higher treewidth = more complex = slower flow)
    base_flow = 1.0 / (1.0 + treewidth)
    
    # Coherence amplifies flow
    # In superfluid state, flow is nearly unlimited
    state = coherence_state(coherence)
    
    if state == "turbulent":
        # Turbulent: flow heavily restricted
        return base_flow * coherence
    elif state == "superfluid":
        # Superfluid: flow amplified by coherence^3
        # (nonlinear enhancement at high coherence)
        return base_flow * (coherence ** 3) * 10.0
    else:
        # Transition: quadratic interpolation
        return base_flow * (coherence ** 2)


def complexity_collapse_factor(coherence: float) -> float:
    """
    Calculate how much complexity collapses at given coherence.
    
    At superfluid state (Ψ → 1), NP complexity collapses to P.
    
    Args:
        coherence: Coherence parameter Ψ
        
    Returns:
        Collapse factor (0 = no collapse, 1 = complete collapse)
    """
    if coherence < COHERENCE_TURBULENT_THRESHOLD:
        # Turbulent: no collapse
        return 0.0
    elif coherence >= COHERENCE_SUPERFLUID_THRESHOLD:
        # Superfluid: near-complete collapse
        return 0.99 + 0.01 * (coherence - COHERENCE_SUPERFLUID_THRESHOLD) / \
               (1.0 - COHERENCE_SUPERFLUID_THRESHOLD)
    else:
        # Transition: sigmoid curve
        t = (coherence - COHERENCE_TURBULENT_THRESHOLD) / \
            (COHERENCE_SUPERFLUID_THRESHOLD - COHERENCE_TURBULENT_THRESHOLD)
        # Sigmoid: smooth transition
        return 1.0 / (1.0 + math.exp(-10 * (t - 0.5)))


def analyze_fluid_system(coherence: float, 
                         treewidth: float = 50.0,
                         radius: float = 0.1) -> Dict[str, Any]:
    """
    Comprehensive analysis of the fluid coherence system.
    
    Args:
        coherence: Coherence parameter Ψ
        treewidth: Problem treewidth (default: 50)
        radius: Vortex radius (default: 0.1)
        
    Returns:
        Dictionary containing all system metrics
    """
    state = coherence_state(coherence)
    complexity = computational_complexity_state(coherence)
    nu_eff = effective_viscosity(coherence)
    lamination = dimensional_lamination_factor(coherence)
    flow_rate = information_flow_rate(coherence, treewidth)
    collapse = complexity_collapse_factor(coherence)
    vortex = vortex_singularity_metrics(radius, coherence)
    
    return {
        'coherence': coherence,
        'state': state,
        'complexity_relation': complexity,
        'effective_viscosity': nu_eff,
        'lamination_factor': lamination,
        'information_flow_rate': flow_rate,
        'complexity_collapse': collapse,
        'vortex_metrics': vortex,
        'treewidth': treewidth,
        'radius': radius,
        'frequency_root': F0_ROOT,
        'coupling_constant': KAPPA_COUPLING
    }


def demonstrate_coherence_transition(start_coherence: float = 0.5,
                                    end_coherence: float = 1.0,
                                    steps: int = 20) -> List[Dict[str, Any]]:
    """
    Demonstrate the transition from turbulent to superfluid state.
    
    Args:
        start_coherence: Starting coherence value
        end_coherence: Ending coherence value
        steps: Number of steps in the transition
        
    Returns:
        List of analysis results at each step
    """
    results = []
    coherence_values = np.linspace(start_coherence, end_coherence, steps)
    
    for psi in coherence_values:
        analysis = analyze_fluid_system(psi)
        results.append(analysis)
    
    return results


# ========== DEMONSTRATION ==========

if __name__ == "__main__":
    print("=" * 70)
    print("FLUID COHERENCE SYSTEM - Gravitational Hierarchy")
    print("=" * 70)
    print()
    print("Implementado la jerarquía de gravedad como un sistema armónico")
    print("donde cada capa es una dimensión de información.")
    print()
    print(f"Frecuencia Raíz (f₀): {F0_ROOT} Hz")
    print(f"Acoplamiento (κ): {KAPPA_COUPLING:.6f} (1/7)")
    print(f"Umbral Turbulento: Ψ < {COHERENCE_TURBULENT_THRESHOLD}")
    print(f"Umbral Superfluidez: Ψ ≥ {COHERENCE_SUPERFLUID_THRESHOLD}")
    print()
    print("=" * 70)
    print()
    
    # Analyze different coherence states
    test_coherences = [0.70, 0.88, 0.92, 0.95, 0.99]
    
    for psi in test_coherences:
        print(f"\nCOHERENCE Ψ = {psi:.2f}")
        print("-" * 70)
        
        analysis = analyze_fluid_system(psi, treewidth=50.0, radius=0.1)
        
        print(f"Estado: {analysis['state'].upper()}")
        print(f"Relación de Complejidad: {analysis['complexity_relation']}")
        print(f"Viscosidad Efectiva (ν_eff): {analysis['effective_viscosity']:.4f}")
        print(f"Factor de Laminación: {analysis['lamination_factor']:.4f}")
        print(f"Tasa de Flujo de Información: {analysis['information_flow_rate']:.6f}")
        print(f"Factor de Colapso de Complejidad: {analysis['complexity_collapse']:.4f}")
        print(f"Fuerza de Singularidad del Vórtice: {analysis['vortex_metrics']['singularity_strength']:.4f}")
        
    print()
    print("=" * 70)
    print("CONCLUSIÓN:")
    print("=" * 70)
    print()
    print("Estado Turbulento (Ψ < 0.88): P ≠ NP")
    print("  → El caos informativo impide la resolución.")
    print()
    print("Estado de Superfluidez (Ψ ≥ 0.95): P = NP")
    print("  → El sistema fluye como una unidad coherente,")
    print("    resolviendo la complejidad de forma instantánea.")
    print()
    print("EL AGUA ES EL MAPA. EL VÓRTICE ES LA PUERTA.")
    print()
