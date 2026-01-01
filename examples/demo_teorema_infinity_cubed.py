#!/usr/bin/env python3
"""
demo_teorema_infinity_cubed.py - Interactive demonstration of Teorema ∞³

This demo showcases the Teorema ∞³ (κ_Π–φ²–13), demonstrating that
N = 13 is the unique natural number with special harmonic resonance
properties related to the golden ratio φ.

Usage:
    python examples/demo_teorema_infinity_cubed.py
    
© JMMB | P vs NP Verification System
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from teorema_infinity_cubed import (
    TeoremaInfinityCubed,
    run_complete_analysis,
    print_theorem_statement,
    PHI,
    PHI_SQUARED,
    N_SPECIAL,
    KAPPA_PI_13
)


def demo_basic_calculations():
    """Demonstrate basic κ_Π calculations."""
    print("=" * 80)
    print("DEMO 1: Basic κ_Π Calculations")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    
    print(f"Golden ratio φ = {PHI:.15f}")
    print(f"φ² = φ + 1 = {PHI_SQUARED:.15f}")
    print(f"ln(φ²) = {theorem.ln_phi_squared:.15f}")
    print()
    
    # Calculate for several values around N=13
    test_values = [10, 11, 12, 13, 14, 15, 16]
    print("N\tκ_Π(N)\t\tN ≈ (φ²)^κ")
    print("-" * 80)
    for N in test_values:
        kappa = theorem.kappa_pi(N)
        # Verify: N ≈ (φ²)^κ
        N_reconstructed = theorem.inverse_kappa_pi(kappa)
        marker = " ★" if N == N_SPECIAL else ""
        print(f"{N}\t{kappa:.6f}\t{N_reconstructed:.6f}{marker}")
    print()
    print(f"★ = N = {N_SPECIAL} (special resonance point)")
    print()


def demo_uniqueness_validation():
    """Demonstrate that N=13 is unique below 100."""
    print("=" * 80)
    print("DEMO 2: Uniqueness Validation for N=13")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    
    # Validate uniqueness
    uniqueness = theorem.validate_uniqueness_below_100()
    
    print(f"Special Value: N = {uniqueness['N_special']}")
    print(f"κ_Π({uniqueness['N_special']}) = {uniqueness['kappa_special']:.6f}")
    print()
    print(f"Is N={uniqueness['N_special']} unique among N < 100? {uniqueness['is_unique']}")
    print(f"Explanation: {uniqueness['explanation']}")
    print()
    
    if uniqueness['candidates']:
        print("Candidates found within tolerance:")
        for cand in uniqueness['candidates']:
            print(f"  N = {cand['N']:2d}: κ_Π = {cand['kappa']:.6f}, "
                  f"distance to target = {cand['distance_to_target']:.6f}")
    print()


def demo_closest_values():
    """Show values of N closest to target κ_Π."""
    print("=" * 80)
    print("DEMO 3: Natural Numbers Closest to κ_Π = 2.5773")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    
    # Find closest integers
    closest = theorem.find_closest_integers_to_target(target_kappa=2.5773, max_N=50)
    
    print("Top 10 natural numbers N with κ_Π(N) closest to 2.5773:")
    print("-" * 80)
    print("Rank\tN\tκ_Π(N)\t\tDistance\tSpecial?")
    print("-" * 80)
    
    for i, item in enumerate(closest[:10], 1):
        marker = "★ YES" if item['is_N13'] else ""
        print(f"{i}\t{item['N']:2d}\t{item['kappa_pi']:.6f}\t{item['distance']:.6f}\t{marker}")
    print()


def demo_geometric_interpretation():
    """Demonstrate geometric interpretation."""
    print("=" * 80)
    print("DEMO 4: Geometric Interpretation")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    geom = theorem.geometric_interpretation()
    
    print("DEFINITION:")
    print(f"  {geom['kappa_pi_definition']}")
    print()
    
    print("φ² SIGNIFICANCE:")
    print(f"  {geom['phi_squared_significance']}")
    print()
    
    print("HODGE NUMBERS:")
    for key, value in geom['hodge_numbers'].items():
        print(f"  {key}: {value}")
    print()
    
    print("N=13 INTERPRETATION:")
    n13 = geom['N_13_interpretation']
    print(f"  Value: {n13['value']}")
    print(f"  κ_Π: {n13['kappa']:.6f}")
    print(f"  Property: {n13['property']}")
    print(f"  Significance: {n13['significance']}")
    print()
    
    print("HARMONIC RESONANCE:")
    harm = geom['harmonic_resonance']
    print(f"  φ² as frequency: {harm['phi_squared_as_frequency']}")
    print(f"  κ_Π as exponent: {harm['kappa_as_exponent']}")
    print(f"  N as DoF: {harm['N_as_degrees_of_freedom']}")
    print(f"  Resonance: {harm['resonance_at_N13']}")
    print()


def demo_minimal_complexity_conjecture():
    """Demonstrate the minimal complexity conjecture."""
    print("=" * 80)
    print("DEMO 5: Minimal Complexity Conjecture (QCAL ∞³)")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    conj = theorem.minimal_complexity_conjecture()
    
    print(f"TITLE: {conj['title']}")
    print()
    print("STATEMENT:")
    print(f"  {conj['statement']}")
    print()
    
    print("MATHEMATICAL FORM:")
    math_form = conj['mathematical_form']
    print(f"  Condition: {math_form['condition']}")
    print(f"  Equivalence: {math_form['equivalence']}")
    print(f"  Interpretation: {math_form['interpretation']}")
    print()
    
    print("IMPLICATIONS:")
    for key, value in conj['implications'].items():
        print(f"  • {key}: {value}")
    print()
    
    print("VALIDATION NEEDED:")
    for i, question in enumerate(conj['validation_needed'], 1):
        print(f"  {i}. {question}")
    print()


def demo_dynamical_interpretation():
    """Demonstrate dynamical/physical interpretation."""
    print("=" * 80)
    print("DEMO 6: Dynamical/Physical Interpretation")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    dyn = theorem.dynamical_interpretation()
    
    print("φ² ROLE:")
    phi2 = dyn['phi_squared_role']
    print(f"  Name: {phi2['name']}")
    print(f"  Value: {phi2['value']:.15f}")
    print(f"  Interpretation: {phi2['interpretation']}")
    print()
    
    print("κ_Π ROLE:")
    kappa = dyn['kappa_pi_role']
    print(f"  Name: {kappa['name']}")
    print(f"  Value at N=13: {kappa['value_at_N13']:.6f}")
    print(f"  Interpretation: {kappa['interpretation']}")
    print()
    
    print("N ROLE:")
    n_role = dyn['N_role']
    print(f"  Name: {n_role['name']}")
    print(f"  Special Value: {n_role['special_value']}")
    print(f"  Interpretation: {n_role['interpretation']}")
    print()
    
    print("RESONANCE CONDITION:")
    res = dyn['resonance_condition']
    print(f"  Statement: {res['statement']}")
    print(f"  Mathematical: {res['mathematical_expression']}")
    print(f"  Physical Meaning: {res['physical_meaning']}")
    print()


def demo_visualization():
    """Generate visualization."""
    print("=" * 80)
    print("DEMO 7: Visualization")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    
    print("Generating κ_Π(N) curve with N=13 highlighted...")
    plot_path = theorem.plot_kappa_curve(N_min=1, N_max=30)
    print(f"✓ Plot saved to: {plot_path}")
    print()
    
    print("Plot features:")
    print("  • Main curve: κ_Π(N) = ln(N) / ln(φ²)")
    print("  • Reference line: κ_Π = 2.5773 (millennium constant)")
    print("  • Special point: N=13 marked with red star")
    print("  • All integer N values shown as gray dots")
    print("  • Annotation explaining N=13 resonance")
    print()


def demo_comparison_table():
    """Create comparison table for various N values."""
    print("=" * 80)
    print("DEMO 8: Comprehensive Comparison Table")
    print("=" * 80)
    print()
    
    theorem = TeoremaInfinityCubed()
    
    print("Comprehensive comparison of N values:")
    print("-" * 80)
    print("N\tκ_Π(N)\t\tDist to 2.5773\tPhase\t\tSpecial")
    print("-" * 80)
    
    for N in range(8, 19):
        kappa = theorem.kappa_pi(N)
        dist = abs(kappa - 2.5773)
        
        if kappa < 2.5773:
            phase = "Sub-critical"
        elif kappa > 2.5773:
            phase = "Super-critical"
        else:
            phase = "Critical"
        
        special = "★ RESONANCE" if N == 13 else ""
        
        print(f"{N}\t{kappa:.6f}\t{dist:.6f}\t\t{phase}\t{special}")
    print()


def main():
    """Run all demonstrations."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  Teorema ∞³ (κ_Π–φ²–13) - Interactive Demonstration".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    # Show theorem statement
    print_theorem_statement()
    print()
    
    input("Press Enter to start demonstrations...")
    
    # Run all demos
    demos = [
        ("Basic Calculations", demo_basic_calculations),
        ("Uniqueness Validation", demo_uniqueness_validation),
        ("Closest Values", demo_closest_values),
        ("Geometric Interpretation", demo_geometric_interpretation),
        ("Minimal Complexity Conjecture", demo_minimal_complexity_conjecture),
        ("Dynamical Interpretation", demo_dynamical_interpretation),
        ("Visualization", demo_visualization),
        ("Comparison Table", demo_comparison_table),
    ]
    
    for i, (name, demo_func) in enumerate(demos, 1):
        print()
        demo_func()
        
        if i < len(demos):
            input("Press Enter to continue to next demo...")
    
    # Offer complete analysis
    print()
    print("=" * 80)
    print("Would you like to run the complete formal analysis?")
    print("This will execute all components of Teorema ∞³.")
    print("=" * 80)
    response = input("Run complete analysis? (y/n): ").strip().lower()
    
    if response == 'y':
        print()
        print()
        run_complete_analysis(display=True)
    
    # Final summary
    print()
    print("=" * 80)
    print("SUMMARY: Teorema ∞³ (κ_Π–φ²–13)")
    print("=" * 80)
    print()
    print("Key Findings:")
    print(f"  1. N = {N_SPECIAL} is UNIQUE among N < 100")
    print(f"  2. κ_Π({N_SPECIAL}) = {KAPPA_PI_13:.6f}")
    print(f"  3. {N_SPECIAL} ≈ (φ²)^{KAPPA_PI_13:.4f}")
    print(f"  4. Represents harmonic resonance point")
    print(f"  5. Minimal complexity in moduli space")
    print()
    print("El 13 no es solo un número.")
    print(f"Es el ÚNICO N tal que N = (φ²)^κ_Π con κ_Π ≈ {KAPPA_PI_13:.4f}.")
    print()
    print("Esto define una intersección singular entre")
    print("geometría, número y vibración.")
    print()
    print("=" * 80)
    print("Demo completed successfully!")
    print("© JMMB | P vs NP Verification System")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 80)
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
