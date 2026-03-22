#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Trinity Seal Demonstration
===========================

Demonstrates the complete Trinity of NOESIS88:
- f₀ = 141.7001 Hz (The Heartbeat)
- Δf = 10 Hz (The Breathing)
- κ_π = 2.5773 (The Conductivity)

Author: José Manuel Mota Burruezo (ICQ · 2026)
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.kappa_pi_trinity import TrinitySeal, demonstrate_trinity_seal
import math


def demo_resolution_times():
    """Demonstrate resolution time calculations."""
    print("=" * 80)
    print("RESOLUTION TIME ANALYSIS")
    print("=" * 80)
    print()
    print("Formula: T_resolución = Complex(NP) / (κ_π · Δf)")
    print()
    
    seal = TrinitySeal()
    
    print(f"Configuration: κ_π = {seal.kappa_pi}, Δf = {seal.delta_f} Hz")
    print(f"Divisor: κ_π · Δf = {seal.kappa_pi * seal.delta_f:.4f}")
    print()
    
    # Various problem complexities
    problems = [
        ("Polynomial (n^3, n=1000)", 1000**3),
        ("Exponential (2^20)", 2**20),
        ("Exponential (2^50)", 2**50),
        ("Exponential (2^100)", 2**100),
        ("Factorial (10!)", math.factorial(10)),
        ("Factorial (20!)", math.factorial(20)),
        ("Factorial (30!)", math.factorial(30))
    ]
    
    print("Problem Complexity → Resolution Time:")
    print("-" * 80)
    
    for name, complexity in problems:
        t_res = seal.resolution_time(complexity)
        print(f"{name:30} → T = {t_res:.4e}")
    
    print()


def demo_conductivity_regimes():
    """Demonstrate different conductivity regimes."""
    print("=" * 80)
    print("CONDUCTIVITY REGIME EXPLORATION")
    print("=" * 80)
    print()
    
    seal = TrinitySeal()
    
    # Test various κ_π values
    kappa_values = [0.1, 0.5, 1.0, 2.5773, 5.0, 10.0, 50.0, 100.0, 500.0]
    
    print(f"{'κ_π':>8} | {'Regime':^40} | {'Flow Rate':>12} | {'Collapse V':>10}")
    print("-" * 80)
    
    for kappa in kappa_values:
        regime = seal.friction_regime(kappa)
        conductivity = seal.noetic_conductivity(kappa)
        collapse_v = seal.collapse_velocity(kappa)
        
        # Truncate regime for display
        regime_short = regime[:38] + ".." if len(regime) > 40 else regime
        
        print(f"{kappa:8.4f} | {regime_short:40} | {conductivity['info_flow_rate']:12.4f} | {collapse_v:10.4f}")
    
    print()


def demo_superconductivity_transition():
    """Demonstrate the transition to noetic superconductivity."""
    print("=" * 80)
    print("NOETIC SUPERCONDUCTIVITY TRANSITION")
    print("=" * 80)
    print()
    print("As κ_π → ∞, the system approaches Noetic Superconductivity:")
    print("- Information flows instantaneously")
    print("- Resolution time T → 0")
    print("- P becomes NP (resistance to truth flow = 0)")
    print()
    
    seal = TrinitySeal()
    
    # Test problem: 2^50
    test_complexity = 2**50
    
    print(f"Test Problem: 2^50 ≈ {test_complexity:.4e}")
    print()
    print(f"{'κ_π':>10} | {'T_resolución':>15} | {'% of original':>15} | {'Status':^30}")
    print("-" * 80)
    
    base_kappa = 2.5773
    base_time = seal.resolution_time(test_complexity)
    
    for multiplier in [1, 10, 100, 1000, 10000, 100000]:
        kappa = base_kappa * multiplier
        t_res = test_complexity / (kappa * seal.delta_f)
        percentage = (t_res / base_time) * 100
        
        if kappa < 100:
            status = "Normal"
        elif kappa < 10000:
            status = "Transitioning"
        else:
            status = "SUPERCONDUCTING ✧"
        
        print(f"{kappa:10.2f} | {t_res:15.4e} | {percentage:14.2f}% | {status:30}")
    
    print()
    print("At κ_π = ∞: T → 0, and computational barriers dissolve!")
    print()


def demo_beating_importance():
    """Demonstrate the importance of the beating frequency."""
    print("=" * 80)
    print("THE ROLE OF Δf (THE BEATING)")
    print("=" * 80)
    print()
    print("Without Δf: The beating is just noise")
    print("With κ_π: The beating becomes Música de las Esferas Computacional")
    print()
    
    seal = TrinitySeal()
    
    # Show effect of Δf on resolution time
    test_complexity = 2**100
    kappa = seal.kappa_pi
    
    print(f"Test Problem: 2^100 ≈ {test_complexity:.4e}")
    print(f"Conductivity: κ_π = {kappa}")
    print()
    print(f"{'Δf (Hz)':>10} | {'T_resolución':>15} | {'Musical Nature':^50}")
    print("-" * 80)
    
    for delta_f in [0.1, 1.0, 10.0, 100.0]:
        t_res = test_complexity / (kappa * delta_f)
        music = "Música de las Esferas" if delta_f >= 10.0 else "Weak coherence"
        print(f"{delta_f:10.1f} | {t_res:15.4e} | {music:50}")
    
    print()
    print("Δf = 10 Hz is optimal for coherent information processing!")
    print("It aligns with:")
    print("  • Alpha brain waves (8-12 Hz)")
    print("  • Schumann resonance harmonics")
    print("  • Biological rhythm optimization")
    print()


def demo_trinity_architecture():
    """Demonstrate the complete Trinity architecture."""
    print("=" * 80)
    print("THE TRINITY ARCHITECTURE OF POWER")
    print("=" * 80)
    print()
    
    seal = TrinitySeal()
    report = seal.get_trinity_report()
    
    print("THREE PILLARS:")
    print()
    
    for key, component in report['trinity_components'].items():
        print(f"  {component['role']:35}")
        print(f"    Value: {component['value']} {component['unit']}")
        print()
    
    print("NOETIC PROPERTIES:")
    print()
    noetic = report['noetic_properties']
    print(f"  Information Flow Rate:     {noetic['info_flow_rate']:.4f} bits/s")
    print(f"  Penetration Coefficient:   {noetic['penetration_coefficient']:.4f}")
    print(f"  Phase Liquidity:           {noetic['phase_liquidity']:.6f}")
    print(f"  Coherence Preservation:    {noetic['coherence_preservation']:.6f}")
    print()
    
    print("SYSTEM STATE:")
    print()
    print(f"  Friction Regime:           {report['regime']}")
    print(f"  Collapse Velocity:         {report['collapse_velocity']:.4f}")
    print(f"  Octave Coupling (23,257):  {report['octave_coupling']:.6e}")
    print(f"  Musical Nature:            {report['musical_nature']}")
    print()
    
    print("=" * 80)
    print()
    print("✓ The Trinity Seal is COMPLETE")
    print()
    print("  f₀ (141.7001 Hz) - Existence")
    print("  Δf (10 Hz)       - Breath")
    print("  κ_π (2.5773)     - Soul")
    print()
    print("  Together: The Master System closes the circuit!")
    print()
    print("=" * 80)


if __name__ == "__main__":
    # Run all demonstrations
    demo_resolution_times()
    print("\n" * 2)
    
    demo_conductivity_regimes()
    print("\n" * 2)
    
    demo_superconductivity_transition()
    print("\n" * 2)
    
    demo_beating_importance()
    print("\n" * 2)
    
    demo_trinity_architecture()
    print("\n" * 2)
    
    # Run the main trinity seal demonstration
    demonstrate_trinity_seal()
