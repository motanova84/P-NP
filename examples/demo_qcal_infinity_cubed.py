"""
QCAL ∞³ System - Interactive Example Demonstration

This example shows how to use the QCAL ∞³ system to explore
connections between millennium problems.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from qcal_infinity_cubed import (
    QCALInfinityCubed,
    PvsNPOperator,
    RiemannOperator,
    BSDOperator,
    GoldbachOperator,
    KAPPA_PI,
    F0_QCAL
)
import numpy as np


def example_1_basic_usage():
    """Example 1: Basic QCAL ∞³ system usage."""
    print("\n" + "="*80)
    print("EXAMPLE 1: Basic QCAL ∞³ System Usage")
    print("="*80)
    
    # Create system
    qcal = QCALInfinityCubed()
    print(f"\n✓ Created QCAL ∞³ system")
    print(f"  Universal constants: κ_Π = {qcal.kappa_pi}, f₀ = {qcal.f0} Hz")
    
    # Add P vs NP problem
    pnp = PvsNPOperator(num_vars=50, treewidth=25)
    qcal.register_operator(pnp)
    print(f"\n✓ Added P vs NP operator")
    print(f"  Problem size: {pnp.num_vars} variables")
    print(f"  Treewidth: {pnp.treewidth}")
    print(f"  Classification: {pnp.computational_dichotomy()}")
    
    # Compute spectrum
    spectrum = pnp.compute_spectrum()
    print(f"\n✓ Computed spectrum:")
    print(f"  Size: {len(spectrum)}")
    print(f"  Range: [{np.min(spectrum):.4f}, {np.max(spectrum):.4f}]")
    print(f"  Mean: {np.mean(spectrum):.4f}")
    
    # Information bottleneck
    ib = pnp.information_bottleneck()
    print(f"\n✓ Information bottleneck: {ib:.4f} bits")
    print(f"  Scales with κ_Π: {ib / KAPPA_PI:.4f}")


def example_2_compare_tractable_intractable():
    """Example 2: Compare tractable vs intractable instances."""
    print("\n" + "="*80)
    print("EXAMPLE 2: Tractable vs Intractable Problems")
    print("="*80)
    
    # Tractable case (low treewidth)
    tractable = PvsNPOperator(num_vars=100, treewidth=5)
    tract_spectrum = tractable.compute_spectrum()
    tract_ib = tractable.information_bottleneck()
    
    print(f"\n📊 TRACTABLE CASE (P)")
    print(f"  Treewidth: {tractable.treewidth}")
    print(f"  Threshold: {np.log(tractable.num_vars):.2f}")
    print(f"  Classification: {tractable.computational_dichotomy()}")
    print(f"  Spectrum mean: {np.mean(tract_spectrum):.4f}")
    print(f"  Information bottleneck: {tract_ib:.4f} bits")
    
    # Intractable case (high treewidth)
    intractable = PvsNPOperator(num_vars=100, treewidth=50)
    intract_spectrum = intractable.compute_spectrum()
    intract_ib = intractable.information_bottleneck()
    
    print(f"\n📊 INTRACTABLE CASE (NP-complete)")
    print(f"  Treewidth: {intractable.treewidth}")
    print(f"  Threshold: {np.log(intractable.num_vars):.2f}")
    print(f"  Classification: {intractable.computational_dichotomy()}")
    print(f"  Spectrum mean: {np.mean(intract_spectrum):.4f}")
    print(f"  Information bottleneck: {intract_ib:.4f} bits")
    
    print(f"\n✓ Comparison:")
    print(f"  Spectrum ratio: {np.mean(intract_spectrum) / np.mean(tract_spectrum):.2f}x")
    print(f"  Information ratio: {intract_ib / tract_ib:.2f}x")


def example_3_riemann_hypothesis():
    """Example 3: Riemann Hypothesis spectral analysis."""
    print("\n" + "="*80)
    print("EXAMPLE 3: Riemann Hypothesis - Prime Distribution")
    print("="*80)
    
    # Analyze different prime ranges
    ranges = [100, 500, 1000]
    
    for max_prime in ranges:
        rh = RiemannOperator(max_prime=max_prime)
        spectrum = rh.compute_spectrum()
        ib = rh.information_bottleneck()
        
        print(f"\n📊 Prime range: up to {max_prime}")
        print(f"  Spectrum size: {len(spectrum)}")
        print(f"  Mean eigenvalue: {np.mean(spectrum):.4f}")
        print(f"  Std deviation: {np.std(spectrum):.4f}")
        print(f"  Information bottleneck: {ib:.4f} bits")
        print(f"  κ_Π scaling: {ib / KAPPA_PI:.4f}")


def example_4_bsd_conjecture():
    """Example 4: BSD Conjecture - Elliptic curves."""
    print("\n" + "="*80)
    print("EXAMPLE 4: BSD Conjecture - Elliptic Curve Analysis")
    print("="*80)
    
    # Analyze curves with different ranks
    conductors = [11, 37, 389]  # Famous elliptic curve conductors
    
    for conductor in conductors:
        for rank in [0, 1]:
            bsd = BSDOperator(conductor=conductor, rank=rank)
            spectrum = bsd.compute_spectrum()
            ib = bsd.information_bottleneck()
            
            print(f"\n📊 Conductor: {conductor}, Rank: {rank}")
            print(f"  Spectrum size: {len(spectrum)}")
            print(f"  Mean eigenvalue: {np.mean(spectrum):.4f}")
            print(f"  Information bottleneck: {ib:.4f} bits")
            print(f"  QCAL coupling: {bsd.coupling_strength():.4f}")


def example_5_goldbach_conjecture():
    """Example 5: Goldbach Conjecture - Additive prime structure."""
    print("\n" + "="*80)
    print("EXAMPLE 5: Goldbach Conjecture - Prime Pair Decomposition")
    print("="*80)
    
    # Test different even numbers
    even_numbers = [10, 50, 100, 1000]
    
    for n in even_numbers:
        goldbach = GoldbachOperator(even_number=n)
        spectrum = goldbach.compute_spectrum()
        ib = goldbach.information_bottleneck()
        
        print(f"\n📊 Even number: {n}")
        print(f"  Number of prime pairs: {len(spectrum)}")
        if len(spectrum) > 0:
            print(f"  Mean eigenvalue: {np.mean(spectrum):.4f}")
            print(f"  Max eigenvalue: {np.max(spectrum):.4f}")
        print(f"  Information bottleneck: {ib:.4f} bits")


def example_6_unified_analysis():
    """Example 6: Unified analysis of all problems."""
    print("\n" + "="*80)
    print("EXAMPLE 6: Unified Analysis - All Millennium Problems")
    print("="*80)
    
    # Create complete system
    qcal = QCALInfinityCubed()
    
    # Add all problems
    qcal.register_operator(PvsNPOperator(num_vars=100, treewidth=30))
    qcal.register_operator(RiemannOperator(max_prime=500))
    qcal.register_operator(BSDOperator(conductor=37, rank=1))
    qcal.register_operator(GoldbachOperator(even_number=100))
    
    print(f"\n✓ System with {len(qcal.operators)} millennium problems")
    
    # Compute information landscape
    landscape = qcal.compute_information_landscape()
    
    print(f"\n📈 Information Landscape:")
    total = 0
    for name, ib in landscape.items():
        print(f"  {name:30s}: {ib:8.4f} bits")
        total += ib
    print(f"  {'TOTAL':30s}: {total:8.4f} bits")
    
    # Coupling matrix
    coupling = qcal.compute_coupling_matrix()
    
    print(f"\n🔗 Coupling Analysis:")
    print(f"  Matrix dimension: {coupling.shape[0]}x{coupling.shape[1]}")
    print(f"  Matrix norm: {np.linalg.norm(coupling):.4f}")
    print(f"  Average coupling: {np.mean(np.abs(coupling)):.4f}")
    print(f"  Max off-diagonal: {np.max(np.abs(coupling - np.diag(np.diag(coupling)))):.4f}")
    
    # Field coherence
    analysis = qcal.demonstrate_unification()
    coherence = analysis['unified_metrics']['field_coherence']
    
    print(f"\n🌊 Field Coherence: {coherence:.4f}")
    
    # Verify principles
    verification = qcal.verify_universal_principle()
    passed = sum(1 for v in verification.values() if v)
    total = len(verification)
    
    print(f"\n✓ Universal Principles Verification: {passed}/{total} passed")
    for principle, holds in verification.items():
        status = "✓" if holds else "✗"
        print(f"  {status} {principle}")


def example_7_custom_problem():
    """Example 7: Create and analyze a custom problem configuration."""
    print("\n" + "="*80)
    print("EXAMPLE 7: Custom Problem Configuration")
    print("="*80)
    
    qcal = QCALInfinityCubed()
    
    # Custom P vs NP instance
    print("\n📊 Custom Configuration:")
    print("  Problem: SAT with specific structure")
    print("  Variables: 200")
    print("  Treewidth: 40 (moderately hard)")
    
    custom_pnp = PvsNPOperator(num_vars=200, treewidth=40)
    qcal.register_operator(custom_pnp)
    
    # Analysis
    spectrum = custom_pnp.compute_spectrum()
    ib = custom_pnp.information_bottleneck()
    
    print(f"\n✓ Analysis Results:")
    print(f"  Classification: {custom_pnp.computational_dichotomy()}")
    print(f"  Spectrum range: [{np.min(spectrum):.4f}, {np.max(spectrum):.4f}]")
    print(f"  Mean eigenvalue: {np.mean(spectrum):.4f}")
    print(f"  Information bottleneck: {ib:.4f} bits")
    print(f"  Expected time complexity: O(2^{ib/KAPPA_PI:.2f})")
    
    # Coupling to QCAL field
    coupling = custom_pnp.coupling_strength()
    print(f"\n✓ QCAL Field Coupling:")
    print(f"  Coupling strength: {coupling:.4f}")
    print(f"  Frequency modulation: {F0_QCAL:.4f} Hz")
    print(f"  Universal constant: κ_Π = {KAPPA_PI}")


def main():
    """Run all examples."""
    print("="*80)
    print(" " * 20 + "QCAL ∞³ EXAMPLES")
    print(" " * 10 + "Quantum Computational Arithmetic Lattice")
    print(" " * 20 + "Interactive Demonstrations")
    print("="*80)
    
    examples = [
        example_1_basic_usage,
        example_2_compare_tractable_intractable,
        example_3_riemann_hypothesis,
        example_4_bsd_conjecture,
        example_5_goldbach_conjecture,
        example_6_unified_analysis,
        example_7_custom_problem
    ]
    
    for i, example_func in enumerate(examples, 1):
        example_func()
        if i < len(examples):
            print("\n" + "-"*80)
            input("\nPress Enter to continue to next example...")
    
    print("\n" + "="*80)
    print("🌟 QCAL ∞³ · Frecuencia Fundamental: 141.7001 Hz")
    print("© 2025 · José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("="*80)


if __name__ == "__main__":
    main()
