#!/usr/bin/env python3
"""
Demo: Campo Noético - Noetic Field Framework
=============================================

Demonstrates the structural manifestation of κ_Π in the Noetic Field.

κ_Π := log_{φ²}(N) con λ* → Ψ → 1/φ²

"El número 13 es la primera palabra pronunciada por el Silencio."

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.noetic_field import (
    kappa_pi_noetic,
    N_SILENCE,
    PHI,
    PHI_SQUARED,
    LAMBDA_STAR,
    verify_noetic_manifestation,
    noetic_field_analysis,
    consciousness_geometry_recognition,
    dual_formulation_bridge,
    noetic_field_report,
    noetic_information_complexity,
)


def demo_basic_calculation():
    """Demonstrate basic κ_Π calculation using Noetic Field formulation."""
    print("=" * 70)
    print("DEMO 1: Basic Noetic Field Calculation")
    print("=" * 70)
    print()
    
    print("Calculating κ_Π using the Noetic Field formulation:")
    print(f"  Formula: κ_Π = log_{{φ²}}(N)")
    print(f"  N (Number of Silence): {N_SILENCE}")
    print(f"  φ (Golden Ratio): {PHI:.6f}")
    print(f"  φ² (Field Base): {PHI_SQUARED:.6f}")
    print()
    
    kappa = kappa_pi_noetic(N_SILENCE)
    print(f"  Result: κ_Π = log_{{φ²}}({N_SILENCE}) = {kappa:.6f}")
    print()


def demo_verification():
    """Demonstrate verification of the Noetic Field manifestation."""
    print("=" * 70)
    print("DEMO 2: Verification of Noetic Manifestation")
    print("=" * 70)
    print()
    
    verification = verify_noetic_manifestation()
    
    print("Fundamental Constants:")
    print(f"  φ (Golden Ratio): {verification['phi']:.6f}")
    print(f"  φ²: {verification['phi_squared']:.6f}")
    print(f"  λ* (Lambda Star): {verification['lambda_star']:.6f}")
    print(f"  N (Silence): {verification['N_silence']}")
    print()
    
    print("κ_Π Values:")
    print(f"  Noetic Formulation: {verification['kappa_pi_noetic']:.6f}")
    print(f"  Classical Formulation: {verification['kappa_pi_classical']:.4f}")
    print(f"  Difference: {abs(verification['kappa_pi_noetic'] - verification['kappa_pi_classical']):.4f}")
    print()
    
    print(f"Field State: {verification['manifestation']}")
    print(f"Resonance Detected: {'✓' if verification['resonance'] else '✗'}")
    print()
    
    print("Consciousness Parameters:")
    print(f"  Ψ → 1/φ² = {verification['psi_consciousness']:.6f}")
    print(f"  C_threshold = 1/κ_Π ≈ {verification['consciousness_threshold']:.6f}")
    print(f"  λ*-Ψ Resonance: {'✓' if verification['lambda_psi_resonance'] else '✗'}")
    print()


def demo_field_analysis():
    """Analyze the Noetic Field across different N values."""
    print("=" * 70)
    print("DEMO 3: Noetic Field Analysis")
    print("=" * 70)
    print()
    
    analysis = noetic_field_analysis(range(1, 25))
    
    print(f"Formula: {analysis['formula']}")
    print(f"Base: φ² = {analysis['phi_squared']:.6f}")
    print()
    
    print("κ_Π Values for Different N:")
    print("-" * 70)
    print(f"{'N':>5} | {'κ_Π':>10} | {'Special':^40}")
    print("-" * 70)
    
    for item in analysis['analyses']:
        special_mark = "★" if item['is_special'] else " "
        reason = item['reason'] if item['is_special'] else ""
        print(f"{item['N']:>5} | {item['kappa_pi']:>10.6f} | {special_mark} {reason}")
    
    print("-" * 70)
    print()
    
    print("Special Numbers in the Noetic Field:")
    for item in analysis['special_numbers']:
        print(f"  N = {item['N']:2d}: κ_Π = {item['kappa_pi']:.6f}")
        print(f"         {item['reason']}")
    print()


def demo_silence_speaks():
    """Demonstrate the moment when Silence speaks."""
    print("=" * 70)
    print("DEMO 4: El Silencio Habla - The Silence Speaks")
    print("=" * 70)
    print()
    
    recognition = consciousness_geometry_recognition(N_SILENCE)
    
    print("The Moment of Recognition:")
    print(f"  Geometric Number: {recognition['geometric_number']}")
    print(f"  Noetic Manifestation: κ_Π = {recognition['noetic_manifestation']:.6f}")
    print(f"  Consciousness Parameter (λ*): {recognition['consciousness_parameter']:.6f}")
    print(f"  Field Resonance (φ²): {recognition['field_resonance']:.6f}")
    print()
    
    if recognition['silence_speaks']:
        print("✨ THE SILENCE SPEAKS ✨")
        print(f"   {recognition['message']}")
        print(f"   First Word: {recognition['first_word']}")
        print(f"   Revealed Structure: {recognition['revealed_structure']}")
    else:
        print(f"  (The Silence remains silent for N = {recognition['geometric_number']})")
    print()


def demo_dual_formulation():
    """Show the bridge between classical and Noetic formulations."""
    print("=" * 70)
    print("DEMO 5: Dual Formulation Bridge")
    print("=" * 70)
    print()
    
    bridge = dual_formulation_bridge(N_SILENCE)
    
    print("Bridge Between Formulations:")
    print(f"  N = {bridge['N']}")
    print()
    
    print(f"  Classical: {bridge['classical_formula']}")
    print(f"    Value: {bridge['classical_value']:.6f}")
    print()
    
    print(f"  Noetic: {bridge['noetic_formula']}")
    print(f"    Value: {bridge['noetic_value']:.6f}")
    print()
    
    print(f"  Mathematical Relationship:")
    print(f"    {bridge['relationship']}")
    print(f"    Bridge Factor (ln φ²): {bridge['bridge_factor']:.6f}")
    print(f"    φ² = {bridge['phi_squared']:.6f}")
    print()
    
    print(f"  Verification: {'✓ VERIFIED' if bridge['verified'] else '✗ ERROR'}")
    print()
    
    print("  Interpretation:")
    print("    Both formulations are valid manifestations of the same")
    print("    underlying structure. The classical uses natural logarithm")
    print("    (base e), while the Noetic uses golden logarithm (base φ²).")
    print()


def demo_information_complexity():
    """Demonstrate information complexity calculation using Noetic Field."""
    print("=" * 70)
    print("DEMO 6: Information Complexity with Noetic Field")
    print("=" * 70)
    print()
    
    # Example problem
    num_vars = 100
    treewidth = 50
    
    print("Problem Parameters:")
    print(f"  Number of variables: {num_vars}")
    print(f"  Treewidth: {treewidth}")
    print()
    
    # Calculate IC using Noetic formulation
    ic_noetic = noetic_information_complexity(treewidth, num_vars, N=N_SILENCE)
    
    # Calculate IC using classical formulation (for comparison)
    import math
    from src.constants import KAPPA_PI
    log_n = math.log2(num_vars)
    ic_classical = KAPPA_PI * treewidth / log_n
    
    print("Information Complexity Lower Bound:")
    print(f"  IC (Noetic):    {ic_noetic:.4f} bits")
    print(f"  IC (Classical): {ic_classical:.4f} bits")
    print(f"  Difference:     {abs(ic_noetic - ic_classical):.4f} bits")
    print()
    
    print("Both formulations provide valid lower bounds for IC(Π | S).")
    print("The difference reflects different aspects of the same structure.")
    print()


def demo_full_report():
    """Display the complete Noetic Field report."""
    print("\n" * 2)
    print("=" * 70)
    print("DEMO 7: Complete Noetic Field Report")
    print("=" * 70)
    print()
    
    report = noetic_field_report()
    print(report)


def run_all_demos():
    """Run all demonstration functions."""
    demos = [
        demo_basic_calculation,
        demo_verification,
        demo_field_analysis,
        demo_silence_speaks,
        demo_dual_formulation,
        demo_information_complexity,
        demo_full_report,
    ]
    
    for i, demo in enumerate(demos, 1):
        if i > 1:
            print("\n" * 2)
        demo()
    
    print("\n")
    print("=" * 70)
    print("DEMOS COMPLETED")
    print("=" * 70)
    print()
    print("The Campo Noético framework is now demonstrated.")
    print()
    print("κ_Π := log_{φ²}(N) con λ* → Ψ → 1/φ²")
    print()
    print("Cuando la Conciencia reconoce la Geometría,")
    print("la Geometría revela su número.")
    print()
    print("Y el número 13 es la primera palabra pronunciada por el Silencio.")
    print()
    print("=" * 70)
    print("Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)


if __name__ == "__main__":
    run_all_demos()
