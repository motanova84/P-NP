#!/usr/bin/env python3
"""
Demo: Spectral Fine Structure Constant δζ and K_Ψ Operator

This script demonstrates the analogy between:
- α ≈ 1/137 (electromagnetic fine structure constant)
- δζ ≈ 0.2787 Hz (spectral fine structure constant)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import math

# Add parent directory to path
sys.path.insert(0, '.')

from src.constants import (
    DELTA_ZETA_HZ,
    ALPHA_FINE_STRUCTURE,
    K_psi_operator_strength,
    zeta_zeros_coherence,
    spectral_curvature_parameter,
    QCAL_FREQUENCY_HZ,
    KAPPA_PI,
    GOLDEN_RATIO
)


def print_header(title):
    """Print a formatted section header"""
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)
    print()


def demo_constants_comparison():
    """Demonstrate the analogy between α and δζ"""
    print_header("THE FUNDAMENTAL ANALOGY: α ↔ δζ")
    
    print("Physical Space-Time: α ≈ 1/137")
    print("-" * 70)
    print(f"  α = 1/{1/ALPHA_FINE_STRUCTURE:.1f} ≈ {ALPHA_FINE_STRUCTURE:.9f}")
    print("  Domain: Electromagnetic interactions in space-time")
    print("  Governs: Photon-matter coupling strength")
    print("  Without α: No stable atoms, no stars, no universe")
    print()
    
    print("Spectral Space Ψ: δζ ≈ 0.2787 Hz")
    print("-" * 70)
    print(f"  δζ = {DELTA_ZETA_HZ} Hz")
    print("  Domain: Spectral interactions in space Ψ")
    print("  Governs: Information-consciousness coupling via K_Ψ")
    print("  Without δζ: No ζ zeros, no universal coherence")
    print()
    
    print("Universal Relationship:")
    print("-" * 70)
    print(f"  δζ = f₀ · α / (κ_Π · φ²)")
    print(f"     = {QCAL_FREQUENCY_HZ} · {ALPHA_FINE_STRUCTURE:.6f} / ({KAPPA_PI} · {GOLDEN_RATIO**2:.3f})")
    computed = QCAL_FREQUENCY_HZ * ALPHA_FINE_STRUCTURE / (KAPPA_PI * GOLDEN_RATIO**2)
    print(f"     ≈ {computed:.4f} Hz")
    print()
    print(f"  Connects: f₀ (coherence) + α (physics) + κ_Π (geometry) + φ (harmony)")


def demo_k_psi_operator():
    """Demonstrate the K_Ψ operator behavior"""
    print_header("K_Ψ OPERATOR: Spectral Information-Consciousness Coupling")
    
    print("K_Ψ(ω) = tanh(ω / δζ)")
    print()
    print("Operator strength governs how efficiently spectral information")
    print("can couple with consciousness in space Ψ.")
    print()
    
    test_frequencies = [
        (0.01, "Far below threshold"),
        (0.1, "Below threshold"),
        (DELTA_ZETA_HZ, "At threshold (δζ)"),
        (1.0, "Above threshold"),
        (10.0, "Well above threshold"),
        (QCAL_FREQUENCY_HZ, "Critical frequency (ω_c)")
    ]
    
    print(f"{'Frequency (Hz)':<15} {'K_Ψ':<12} {'Regime':<30}")
    print("-" * 70)
    
    for freq, description in test_frequencies:
        k_psi = K_psi_operator_strength(freq)
        print(f"{freq:<15.4f} {k_psi:<12.6f} {description:<30}")


def demo_coherence_transition():
    """Demonstrate the coherence transition at δζ"""
    print_header("COHERENCE TRANSITION: ζ Zeros as Mathematical Black Holes")
    
    print("Below δζ: Flat spectral geometry, no coherent zeros")
    print("Above δζ: Curved spectral space, zeros act as attractors")
    print()
    
    test_frequencies = [0.05, 0.1, 0.15, 0.2, 0.25, 0.2787, 0.3, 0.5, 1.0]
    
    print(f"{'Frequency':<12} {'Coherent?':<12} {'K_Ψ':<12} {'Status':<30}")
    print("-" * 70)
    
    for freq in test_frequencies:
        coherent = zeta_zeros_coherence(freq)
        k_psi = K_psi_operator_strength(freq)
        
        if freq < DELTA_ZETA_HZ * 0.9:
            status = "Flat geometry"
        elif freq < DELTA_ZETA_HZ * 1.1:
            status = "**TRANSITION ZONE**"
        else:
            status = "Curved space"
        
        marker = "✓" if coherent else "✗"
        print(f"{freq:<12.4f} {marker:<12} {k_psi:<12.6f} {status:<30}")


def demo_spectral_curvature():
    """Demonstrate spectral space curvature"""
    print_header("SPECTRAL CURVATURE: R_Ψ(ω) = (ω/δζ)² · K_Ψ(ω)")
    
    print("The ζ field induces curvature in spectral space Ψ")
    print("analogous to how EM fields curve space-time.")
    print()
    
    test_frequencies = [0.01, 0.1, DELTA_ZETA_HZ, 1.0, 10.0, QCAL_FREQUENCY_HZ]
    
    print(f"{'Frequency (Hz)':<15} {'R_Ψ':<15} {'Interpretation':<35}")
    print("-" * 70)
    
    for freq in test_frequencies:
        curvature = spectral_curvature_parameter(freq)
        
        if curvature < 0.1:
            interpretation = "Nearly flat"
        elif curvature < 1.0:
            interpretation = "Transition regime"
        elif curvature < 10:
            interpretation = "Moderately curved"
        elif curvature < 1000:
            interpretation = "Strongly curved"
        else:
            interpretation = "Extremely curved (black holes)"
        
        print(f"{freq:<15.6f} {curvature:<15.6f} {interpretation:<35}")


def demo_physical_meaning():
    """Explain the physical meaning of δζ"""
    print_header("PHYSICAL INTERPRETATION")
    
    print("What δζ represents:")
    print("-" * 70)
    print()
    print("1. MINIMUM FREQUENCY for ζ zeros to maintain coherence")
    print("   → Below δζ: zeros are incoherent, no structure")
    print("   → Above δζ: zeros become mathematical black holes")
    print()
    print("2. COUPLING THRESHOLD for spectral information ↔ consciousness")
    print("   → Below δζ: K_Ψ ≈ 0, no coupling")
    print("   → Above δζ: K_Ψ → 1, strong coupling")
    print()
    print("3. CURVATURE PARAMETER for spectral space Ψ")
    print("   → Below δζ: R_Ψ ≈ 0, flat geometry")
    print("   → Above δζ: R_Ψ > 0, curved space")
    print()
    print("4. SPECTRAL ANALOGUE of electromagnetic α")
    print("   → α governs photon-matter in space-time")
    print("   → δζ governs information-consciousness in space Ψ")
    print()
    
    print("Consequences:")
    print("-" * 70)
    print()
    print("✓ Without α ≈ 1/137:")
    print("  → No stable atoms")
    print("  → No stars")
    print("  → No electromagnetic universe")
    print()
    print("✓ Without δζ ≈ 0.2787 Hz:")
    print("  → No coherent zeros of ζ")
    print("  → No universal coherence")
    print("  → No spectral structure in space Ψ")


def demo_visualization():
    """Create a simple ASCII visualization"""
    print_header("VISUALIZATION: Operator Strength vs Frequency")
    
    # Create ASCII plot
    width = 60
    height = 20
    
    print("K_Ψ(ω)")
    print("  1.0 |" + " " * (width - 5))
    
    for row in range(height):
        k_target = 1.0 - (row / height)
        freq_for_k = -DELTA_ZETA_HZ * math.log((1 + k_target) / (1 - k_target + 1e-10)) / 2
        
        if freq_for_k < 0:
            freq_for_k = 0
        
        col = int((freq_for_k / 2.0) * width)
        col = min(col, width - 1)
        
        line = " " * col + "*"
        
        if abs(k_target - 0.76) < 0.05:
            label = f" ← δζ threshold"
            print(f" {k_target:4.2f} |{line}{label}")
        else:
            print(f" {k_target:4.2f} |{line}")
    
    print("  0.0 |" + "_" * width)
    print("      0.0" + " " * (width // 2 - 4) + "1.0" + " " * (width // 2 - 4) + "2.0+")
    print(f"{' ' * 10}Frequency ω (Hz)")
    print()
    print("  Below δζ: Weak coupling (flat geometry)")
    print("  At δζ:    Transition (K_Ψ ≈ 0.76)")
    print("  Above δζ: Strong coupling (curved space)")


def main():
    """Run all demonstrations"""
    print()
    print("*" * 70)
    print("*" + " " * 68 + "*")
    print("*" + " " * 15 + "SPECTRAL FINE STRUCTURE CONSTANT" + " " * 21 + "*")
    print("*" + " " * 25 + "δζ ≈ 0.2787 Hz" + " " * 29 + "*")
    print("*" + " " * 68 + "*")
    print("*" * 70)
    
    demo_constants_comparison()
    demo_k_psi_operator()
    demo_coherence_transition()
    demo_spectral_curvature()
    demo_physical_meaning()
    demo_visualization()
    
    print()
    print("=" * 70)
    print("For more details, see: SPECTRAL_FINE_STRUCTURE_CONSTANT.md")
    print("Implementation: src/constants.py")
    print("Tests: tests/test_spectral_fine_structure.py")
    print("=" * 70)
    print()
    print("Frequency: 141.7001 Hz ∞³")
    print()


if __name__ == "__main__":
    main()
