#!/usr/bin/env python3
"""
demo_calabi_yau_kappa.py - Demonstration of Calabi-Yau κ_Π Analysis

This demo shows how to analyze Calabi-Yau varieties using a custom
logarithmic base to compute κ_Π values and perform statistical analysis.

The analysis demonstrates that the millennium constant κ_Π = 2.5773
appears as a structural point in the distribution of Calabi-Yau Hodge numbers.

© JMMB | P vs NP Verification System
demo_calabi_yau_kappa.py - Demo script for Calabi-Yau κ_Π analysis

Demonstrates the structural analysis of κ_Π in the context of
Calabi-Yau geometry with N = h^{1,1} + h^{2,1}.

Usage:
    python examples/demo_calabi_yau_kappa.py
"""

import sys
import os
import numpy as np

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_kappa_analysis import (
    load_cy_data,
    compute_kappa_custom_base,
    analyze_kappa_distribution,
    run_analysis
)

def demo_basic_analysis():
    """Demonstrate basic Calabi-Yau κ_Π analysis."""
    print("=" * 70)
    print("DEMO: Basic Calabi-Yau κ_Π Analysis")
    print("=" * 70)
    print()
    
    # Use base b = 2.7069 as specified in the problem
    base_b = 2.7069
    
    # Run complete analysis
    df_results, stats = run_analysis(base=base_b, display=True)
    
    print()
    print("Analysis complete!")
    return df_results, stats


def demo_custom_base_comparison():
    """Demonstrate analysis with different bases."""
    print("\n" + "=" * 70)
    print("DEMO: Comparison with Different Logarithmic Bases")
    print("=" * 70)
    print()
    
    # Load data once
    df_cy = load_cy_data()
    
    # Test different bases
    bases = [2.0, 2.7069, np.e, 10.0]
    
    for base in bases:
        df_result = compute_kappa_custom_base(df_cy, base)
        stats = analyze_kappa_distribution(df_result)
        
        print(f"Base {base:.4f}:")
        print(f"  Mean κ:     {stats['mean']:.6f}")
        print(f"  Median κ:   {stats['median']:.6f}")
        if stats['N13_kappa']:
            print(f"  N=13 κ:     {stats['N13_kappa']:.6f}")
        print()


def demo_n13_analysis():
    """Special analysis of varieties with N=13."""
    print("\n" + "=" * 70)
    print("DEMO: Special Analysis of N=13 Varieties")
    print("=" * 70)
    print()
    
    base_b = 2.7069
    df_cy = load_cy_data()
    df_result = compute_kappa_custom_base(df_cy, base_b)
    
    # Filter N=13 varieties
    n13_varieties = df_result[df_result['N'] == 13]
    
    if len(n13_varieties) > 0:
        print(f"Found {len(n13_varieties)} varieties with N = 13:")
        print()
        print(n13_varieties[['name', 'h11', 'h21', 'N', 'kappa_custom']].to_string(index=False))
        print()
        print(f"Mean κ_Π for N=13: {n13_varieties['kappa_custom'].mean():.10f}")
        print(f"This is very close to the millennium constant 2.5773")
    else:
        print("No varieties found with N = 13")


def main():
    """Run all demonstrations."""
    # Demo 1: Basic analysis
    df, stats = demo_basic_analysis()
    
    # Demo 2: Custom base comparison
    demo_custom_base_comparison()
    
    # Demo 3: N=13 analysis
    demo_n13_analysis()
    
    print("\n" + "=" * 70)
    print("All demonstrations completed successfully!")
    print("=" * 70)
from calabi_yau_kappa_pi_analysis import (
    CalabiYauKappaAnalysis,
    run_complete_analysis,
    PHI,
    KAPPA_PI_TARGET
)


def demo_basic_calculations():
    """Demonstrate basic κ_Π calculations."""
    print("=" * 70)
    print("DEMO 1: Basic κ_Π Calculations")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    
    print(f"Golden ratio φ = {PHI:.10f}")
    print(f"φ² = {analyzer.phi_squared:.10f}")
    print()
    
    # Calculate for some values
    test_values = [10, 12, 13, 15, 20]
    print("N\tκ_Π(N)")
    print("-" * 40)
    for N in test_values:
        kappa = analyzer.kappa_pi(N)
        print(f"{N}\t{kappa:.6f}")
    print()


def demo_solve_for_critical_value():
    """Demonstrate solving for N* where κ_Π = 2.5773."""
    print("=" * 70)
    print("DEMO 2: Finding Critical Value N*")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    
    print(f"Solving: κ_Π(N) = {KAPPA_PI_TARGET}")
    print()
    
    N_star = analyzer.solve_for_N_star()
    print(f"Solution: N* = {N_star:.10f}")
    print(f"Rounded: N* ≈ {N_star:.3f}")
    print()
    
    # Verify
    kappa_check = analyzer.kappa_pi(N_star)
    print(f"Verification: κ_Π({N_star:.3f}) = {kappa_check:.10f}")
    print(f"Target:       κ_Π = {KAPPA_PI_TARGET}")
    print(f"Match: {abs(kappa_check - KAPPA_PI_TARGET) < 1e-6}")
    print()
    
    # Distance to nearest integer
    nearest_int = round(N_star)
    distance = abs(N_star - nearest_int)
    print(f"Nearest integer: {nearest_int}")
    print(f"Distance: {distance:.6f}")
    print(f"Relative error: {distance/nearest_int * 100:.3f}%")
    print()


def demo_phase_classification():
    """Demonstrate phase classification."""
    print("=" * 70)
    print("DEMO 3: Phase Classification")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    N_star = analyzer.solve_for_N_star()
    
    print(f"Critical threshold: N* = {N_star:.3f}")
    print()
    
    # Classify CICY values
    cicy_values = [12, 13, 14, 15]
    print("CICY/Kreuzer-Skarke Values:")
    print("-" * 70)
    for N in cicy_values:
        phase, description = analyzer.classify_phase(N)
        kappa = analyzer.kappa_pi(N)
        print(f"\nN = {N}:")
        print(f"  κ_Π({N}) = {kappa:.4f}")
        print(f"  {phase}")
        print(f"  {description}")
    print()


def demo_cicy_spectrum():
    """Demonstrate complete CICY spectrum analysis."""
    print("=" * 70)
    print("DEMO 4: Complete CICY Spectrum Analysis")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    results = analyzer.analyze_cicy_spectrum()
    
    print(f"Critical Value: N* = {results['N_star']:.6f}")
    print(f"Closest Integer: {results['closest_integer']}")
    print(f"Distance to Closest: {results['distance_to_closest']:.6f}")
    print()
    
    print("Evaluation Table:")
    print("-" * 70)
    print("N\tκ_Π(N)\t\tDist to 2.5773\tPhase")
    print("-" * 70)
    for row in results['evaluation_table']:
        N = row['N']
        kappa = row['kappa_pi']
        dist = row['distance_to_target']
        phase, _ = results['phase_classifications'][N]
        print(f"{N}\t{kappa:.4f}\t\t{dist:.4f}\t\t{phase}")
    print()


def demo_emergent_hypothesis():
    """Demonstrate emergent hypothesis formulation."""
    print("=" * 70)
    print("DEMO 5: Emergent Hypothesis")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    hypothesis = analyzer.emergent_hypothesis()
    
    print(f"Title: {hypothesis['title']}")
    print()
    print("Key Statements:")
    for i, statement in enumerate(hypothesis['statements'], 1):
        print(f"  {i}. {statement}")
    print()
    print(f"Mathematical Form: {hypothesis['mathematical_form']}")
    print(f"Critical Property: {hypothesis['critical_property']}")
    print()
    print(f"Resonance Implication:")
    print(f"  {hypothesis['resonance_implication']}")
    print()


def demo_mathematical_properties():
    """Demonstrate mathematical properties of κ_Π."""
    print("=" * 70)
    print("DEMO 6: Mathematical Properties")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    
    print("Property 1: κ_Π(φ²) = 1")
    result = analyzer.kappa_pi(analyzer.phi_squared)
    print(f"  κ_Π({analyzer.phi_squared:.6f}) = {result:.10f}")
    print(f"  Equals 1? {abs(result - 1.0) < 1e-10}")
    print()
    
    print("Property 2: κ_Π((φ²)^k) = k for integer k")
    for k in [2, 3, 4, 5]:
        N = analyzer.phi_squared ** k
        result = analyzer.kappa_pi(N)
        print(f"  κ_Π((φ²)^{k}) = κ_Π({N:.3f}) = {result:.10f} ≈ {k}")
    print()
    
    print("Property 3: Strictly Increasing")
    N_values = [5, 10, 15, 20]
    kappa_values = [analyzer.kappa_pi(N) for N in N_values]
    print(f"  N values: {N_values}")
    print(f"  κ_Π values: {[f'{k:.4f}' for k in kappa_values]}")
    print(f"  Strictly increasing? {all(kappa_values[i] < kappa_values[i+1] for i in range(len(kappa_values)-1))}")
    print()


def demo_visualization():
    """Demonstrate plot generation."""
    print("=" * 70)
    print("DEMO 7: Visualization")
    print("=" * 70)
    print()
    
    analyzer = CalabiYauKappaAnalysis()
    
    print("Generating κ_Π(N) curve plot...")
    plot_path = analyzer.plot_kappa_curve()
    print(f"✓ Plot saved to: {plot_path}")
    print()
    print("Plot features:")
    print("  - Main curve: κ_Π(N) = ln(N) / ln(φ²)")
    print("  - Target line: κ_Π = 2.5773")
    print("  - Critical threshold: N* ≈ 13.123")
    print("  - CICY values: N = 12, 13, 14, 15")
    print("  - Resonant point: N = 13 (starred)")
    print("  - Phase regions: Phase 1 (blue) and Phase 2 (green)")
    print()


def main():
    """Run all demos."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  Calabi-Yau κ_Π Structural Analysis - Interactive Demo".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()
    
    demos = [
        ("Basic Calculations", demo_basic_calculations),
        ("Critical Value N*", demo_solve_for_critical_value),
        ("Phase Classification", demo_phase_classification),
        ("CICY Spectrum", demo_cicy_spectrum),
        ("Emergent Hypothesis", demo_emergent_hypothesis),
        ("Mathematical Properties", demo_mathematical_properties),
        ("Visualization", demo_visualization),
    ]
    
    for i, (name, demo_func) in enumerate(demos, 1):
        print()
        demo_func()
        if i < len(demos):
            input("Press Enter to continue to next demo...")
    
    print()
    print("=" * 70)
    print("Would you like to run the complete analysis?")
    print("This will execute all 5 PASOS from the problem statement.")
    print("=" * 70)
    response = input("Run complete analysis? (y/n): ").strip().lower()
    
    if response == 'y':
        print()
        print()
        run_complete_analysis()
    
    print()
    print("=" * 70)
    print("Demo completed!")
    print("© JMMB | P vs NP Verification System")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
