#!/usr/bin/env python3
"""
demo_cy_complexity.py - Interactive demonstration of CY complexity framework

Demonstrates the spectral complexity barrier in Calabi-Yau Ricci-flat
metric construction as a conditional approach to P vs NP.

© JMMB | P vs NP Verification System
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from cy_rf_construct import (
    CalabiYauManifold,
    SpectralComplexityMeasure,
    CYRFConstructProblem,
    ConditionalHardness,
    ExperimentalValidation
)
import math


def demo_basic_concepts():
    """Demonstrate basic concepts of the framework."""
    print("=" * 70)
    print("DEMO 1: BASIC CONCEPTS")
    print("=" * 70)
    print()
    
    print("Creating Calabi-Yau manifolds with different Hodge numbers...")
    print()
    
    manifolds = [
        CalabiYauManifold(h_11=1, h_21=101, name="Quintic"),
        CalabiYauManifold(h_11=4, h_21=4, name="Symmetric"),
        CalabiYauManifold(h_11=19, h_21=19, name="Self-Mirror"),
    ]
    
    for m in manifolds:
        print(f"{m.name}:")
        print(f"  Hodge numbers: h^{{1,1}} = {m.h_11}, h^{{2,1}} = {m.h_21}")
        print(f"  Total moduli: {m.total_moduli}")
        print(f"  Euler char χ: {m.euler_char}")
        
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        print(f"  κ_Π = log₂({m.total_moduli}) = {kappa:.4f}")
        
        size = SpectralComplexityMeasure.moduli_space_size(m)
        print(f"  Min moduli space size: |M| ≥ {size}")
        print()


def demo_spectral_complexity():
    """Demonstrate spectral complexity measure properties."""
    print("=" * 70)
    print("DEMO 2: SPECTRAL COMPLEXITY MEASURE κ_Π")
    print("=" * 70)
    print()
    
    print("Demonstrating key properties of κ_Π:")
    print()
    
    # Property 1: Monotonicity
    print("1. MONOTONICITY")
    print("   κ_Π increases with total moduli dimension")
    print()
    
    moduli_values = [2, 8, 13, 32, 64, 128]
    
    for n in moduli_values:
        # Create manifold with total moduli = n
        h_11 = n // 2
        h_21 = n - h_11
        m = CalabiYauManifold(h_11=h_11, h_21=h_21, name=f"Moduli-{n}")
        
        kappa = SpectralComplexityMeasure.kappa_pi(m)
        print(f"   Total moduli = {n:3d} → κ_Π = {kappa:.4f}")
    
    print()
    
    # Property 2: Special value log₂(13)
    print("2. SPECIAL VALUE: log₂(13)")
    print(f"   κ_Π = log₂(13) ≈ {math.log2(13):.6f}")
    print()
    
    m_special = CalabiYauManifold(h_11=6, h_21=7, name="Special-13")
    kappa_special = SpectralComplexityMeasure.kappa_pi(m_special)
    print(f"   Manifold with h^{{1,1}}=6, h^{{2,1}}=7:")
    print(f"   κ_Π = {kappa_special:.6f}")
    print(f"   Difference from log₂(13): {abs(kappa_special - math.log2(13)):.2e}")
    print()


def demo_cy_rf_problem():
    """Demonstrate CY-RF-CONSTRUCT problem."""
    print("=" * 70)
    print("DEMO 3: CY-RF-CONSTRUCT PROBLEM")
    print("=" * 70)
    print()
    
    # Create problem instance
    manifold = CalabiYauManifold(h_11=1, h_21=101, name="Quintic")
    epsilon = 0.01
    
    problem = CYRFConstructProblem(manifold, epsilon)
    
    print(f"Problem Instance:")
    print(f"  Manifold: {manifold.name}")
    print(f"  h^{{1,1}} = {manifold.h_11}, h^{{2,1}} = {manifold.h_21}")
    print(f"  Error tolerance ε = {epsilon}")
    print()
    
    # Verify in NP
    is_np, explanation = problem.is_in_np()
    print("Complexity Class:")
    print(f"  CY-RF-CONSTRUCT ∈ NP: {is_np}")
    print()
    
    # Analyze search space
    complexity = problem.get_search_space_complexity()
    
    print("Search Space Analysis:")
    print(f"  Spectral complexity κ_Π: {complexity['kappa_pi']:.4f}")
    print(f"  Min moduli space size: {complexity['min_moduli_space_size']}")
    print(f"  Min search time: 2^κ_Π ≈ {complexity['min_search_time_exponential']:.2e}")
    print()
    
    # Show exponential growth
    print("Exponential Barrier:")
    for scale in [1, 2, 5, 10]:
        m = CalabiYauManifold(h_11=scale, h_21=scale*10)
        p = CYRFConstructProblem(m, 0.01)
        c = p.get_search_space_complexity()
        print(f"  h^{{1,1}}={scale:2d}, h^{{2,1}}={scale*10:3d}: "
              f"κ_Π={c['kappa_pi']:5.2f}, Time ≥ {c['min_search_time_exponential']:10.2e}")
    print()


def demo_conditional_hardness():
    """Demonstrate conditional hardness theorem."""
    print("=" * 70)
    print("DEMO 4: CONDITIONAL HARDNESS (Theorem 6.2)")
    print("=" * 70)
    print()
    
    print("Conjecture 6.1: SAT ≤_p CY-RF-CONSTRUCT")
    print()
    
    print("Analyzing hypothetical SAT → CY reduction:")
    print()
    
    sat_sizes = [10, 50, 100, 200, 500]
    
    for n_vars in sat_sizes:
        reduction = ConditionalHardness.analyze_reduction(n_vars)
        
        print(f"SAT with {n_vars:3d} variables:")
        print(f"  → CY manifold with {reduction['cy_total_moduli']:3d} total moduli")
        print(f"  → κ_Π = {reduction['kappa_pi']:.4f}")
        print(f"  → Search space ≥ 2^{reduction['kappa_pi']:.2f} ≈ "
              f"{2**reduction['kappa_pi']:.2e}")
        print()
    
    print("Theorem 6.2 (Conditional):")
    print("  If Conjecture 6.1 holds, then:")
    print("    CY-RF-CONSTRUCT ∈ P ⟹ P = NP")
    print()
    print("  Contrapositive:")
    print("    P ≠ NP ⟹ CY-RF-CONSTRUCT ∉ P")
    print()
    print("  Interpretation:")
    print("    κ_Π acts as a spectral barrier preventing polynomial-time")
    print("    construction of Ricci-flat metrics on CY manifolds.")
    print()


def demo_experimental_validation():
    """Demonstrate experimental validation on CY database."""
    print("=" * 70)
    print("DEMO 5: EXPERIMENTAL VALIDATION")
    print("=" * 70)
    print()
    
    # Load sample database
    manifolds = ExperimentalValidation.create_kreuzer_skarke_sample()
    stats = ExperimentalValidation.compute_statistics(manifolds)
    
    print(f"Kreuzer-Skarke Database Sample: {stats['num_manifolds']} manifolds")
    print()
    
    print("Statistical Analysis of κ_Π:")
    print(f"  Mean:     {stats['kappa_pi_mean']:.4f}")
    print(f"  Std Dev:  {stats['kappa_pi_std']:.4f}")
    print(f"  Min:      {stats['kappa_pi_min']:.4f}")
    print(f"  Max:      {stats['kappa_pi_max']:.4f}")
    print()
    
    print(f"Moduli Dimensions:")
    print(f"  Mean:     {stats['moduli_dim_mean']:.2f}")
    print(f"  Std Dev:  {stats['moduli_dim_std']:.2f}")
    print()
    
    print("Complete Database:")
    print()
    print(f"{'Manifold':<25} {'h^{1,1}':>7} {'h^{2,1}':>7} {'Total':>6} {'κ_Π':>7} {'|M| ≥':>12}")
    print("-" * 70)
    
    for m, kappa in zip(manifolds, stats['kappa_values']):
        size = SpectralComplexityMeasure.moduli_space_size(m)
        print(f"{m.name:<25} {m.h_11:7d} {m.h_21:7d} {m.total_moduli:6d} "
              f"{kappa:7.3f} {size:12d}")
    
    print()
    print(f"Special value log₂(13): {stats['special_value_log2_13']:.6f}")
    print()


def demo_complete_framework():
    """Demonstrate the complete framework end-to-end."""
    print("=" * 70)
    print("DEMO 6: COMPLETE FRAMEWORK")
    print("=" * 70)
    print()
    
    print("End-to-end demonstration of the CY complexity framework:")
    print()
    
    # Step 1: Define CY manifold
    print("Step 1: Define Calabi-Yau manifold")
    manifold = CalabiYauManifold(h_11=2, h_21=86, name="Bi-cubic")
    print(f"  {manifold.name}: h^{{1,1}}={manifold.h_11}, h^{{2,1}}={manifold.h_21}")
    print(f"  Total moduli: {manifold.total_moduli}")
    print()
    
    # Step 2: Compute κ_Π
    print("Step 2: Compute spectral complexity κ_Π")
    kappa = SpectralComplexityMeasure.kappa_pi(manifold)
    print(f"  κ_Π = log₂({manifold.total_moduli}) = {kappa:.4f}")
    print()
    
    # Step 3: Analyze moduli space
    print("Step 3: Analyze moduli space size")
    size = SpectralComplexityMeasure.moduli_space_size(manifold)
    print(f"  |M_X| ≥ 2^κ_Π = {size}")
    print()
    
    # Step 4: Create CY-RF problem
    print("Step 4: Formulate CY-RF-CONSTRUCT problem")
    epsilon = 0.001
    problem = CYRFConstructProblem(manifold, epsilon)
    print(f"  Error tolerance: ε = {epsilon}")
    is_np, _ = problem.is_in_np()
    print(f"  Problem in NP: {is_np}")
    print()
    
    # Step 5: Search complexity
    print("Step 5: Determine search complexity")
    complexity = problem.get_search_space_complexity()
    print(f"  Without structure: T ≥ 2^κ_Π ≈ {complexity['min_search_time_exponential']:.2e}")
    print()
    
    # Step 6: Conditional hardness
    print("Step 6: Apply conditional hardness theorem")
    print(f"  If SAT ≤_p CY-RF-CONSTRUCT, then:")
    print(f"    CY-RF-CONSTRUCT ∈ P ⟹ P = NP")
    print(f"  Therefore: κ_Π acts as spectral barrier")
    print()
    
    print("=" * 70)
    print("✅ Complete framework demonstration successful")
    print("=" * 70)


def main():
    """Run all demonstrations."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  SPECTRAL COMPLEXITY BARRIER IN CALABI-YAU METRIC CONSTRUCTION  ".center(68) + "║")
    print("║" + "  A Conditional Approach to P vs NP  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "  Interactive Demonstration  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()
    
    demos = [
        ("Basic Concepts", demo_basic_concepts),
        ("Spectral Complexity Measure", demo_spectral_complexity),
        ("CY-RF-CONSTRUCT Problem", demo_cy_rf_problem),
        ("Conditional Hardness", demo_conditional_hardness),
        ("Experimental Validation", demo_experimental_validation),
        ("Complete Framework", demo_complete_framework),
    ]
    
    for i, (name, demo_func) in enumerate(demos, 1):
        print()
        demo_func()
        
        if i < len(demos):
            input("\nPress Enter to continue to next demo...")
            print("\n" * 2)
    
    print()
    print("=" * 70)
    print("ALL DEMONSTRATIONS COMPLETE")
    print("=" * 70)
    print()
    print("Summary:")
    print("  • κ_Π is a well-defined spectral complexity measure")
    print("  • CY-RF-CONSTRUCT ∈ NP with exponential search space")
    print("  • Conditional hardness connects to P vs NP")
    print("  • Experimental validation on CY database")
    print("  • Framework provides geometric perspective on complexity")
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
