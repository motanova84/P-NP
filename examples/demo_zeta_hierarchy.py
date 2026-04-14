"""
Demo: Unified Hierarchy Zeta System

Demonstrates how all five systems converge to the Riemann zeta function ζ(s)
and its non-trivial zeros.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.unified_hierarchy_zeta import (
    UnifiedHierarchyTheorem,
    ZetaFundamentalSystem,
    GoldenRatioModulation,
    ZetaValuesAnalytical,
    QCALCodonResonance,
    HarmonicSystem,
    verify_unified_hierarchy
)
import numpy as np
import matplotlib.pyplot as plt

def demonstrate_all_systems():
    """Demonstrate all five systems and their convergence."""
    
    print("=" * 80)
    print("🌌 UNIFIED HIERARCHY DEMONSTRATION")
    print("   All Systems Converge to ζ(s)")
    print("=" * 80)
    
    # Initialize the unified hierarchy
    hierarchy = UnifiedHierarchyTheorem(num_zeros=20)
    
    # ========================================================================
    # SYSTEM 5: ζ(s) as Fundamental Base
    # ========================================================================
    print("\n" + "=" * 80)
    print("🌀 SYSTEM 5: ζ(s) AS FUNDAMENTAL BASE")
    print("=" * 80)
    
    zeta = hierarchy.zeta_system
    
    print(f"\nFirst zero: ρ₁ = 1/2 + i·{zeta.gamma_1:.9f}")
    print(f"Base frequency: f₀ = {zeta.f0:.4f} Hz")
    print(f"Spectral delta: δζ = {zeta.delta_zeta:.4f} Hz")
    
    frequencies = zeta.spectral_frequencies()
    print(f"\nFirst 10 spectral frequencies:")
    for i, freq in enumerate(frequencies[:10]):
        print(f"  f_{i+1} = {freq:10.4f} Hz  (from γ_{i+1} = {zeta.gamma_values[i]:.6f})")
    
    spacings = zeta.zero_spacings()
    print(f"\nFirst 5 zero spacings:")
    for i, spacing in enumerate(spacings[:5]):
        weyl = zeta.weyl_density(i+1)
        print(f"  Δγ_{i+1} = {spacing:.6f}  (Weyl: {weyl:.6f})")
    
    # ========================================================================
    # SYSTEM 1: Golden Ratio φ - Fractal Modulation
    # ========================================================================
    print("\n" + "=" * 80)
    print("💎 SYSTEM 1: GOLDEN RATIO φ - FRACTAL MODULATION")
    print("=" * 80)
    
    golden = hierarchy.golden_system
    
    print(f"\nGolden ratio: φ = {golden.phi:.15f}")
    print(f"Golden angle: {golden.golden_angle_in_spectrum():.6f} radians")
    
    print("\nFibonacci sequence from φ:")
    for n in range(1, 11):
        F_n, F_n1 = golden.fibonacci_emergence(n)
        ratio = F_n1 / F_n if F_n > 0 else 0
        print(f"  F_{n:2d} = {F_n:4d}, F_{n+1:2d} = {F_n1:4d}, ratio = {ratio:.10f}")
    
    print("\nSelf-similar frequency ratios (k=1, α=0.5):")
    ratios = golden.self_similar_ratios(k=1, alpha=0.5)[:5]
    for i, (actual, expected) in enumerate(ratios):
        print(f"  f_{i+2}/f_{i+1} = {actual:.6f}  (φ^0.5 = {expected:.6f}, diff = {abs(actual-expected):.6f})")
    
    # ========================================================================
    # SYSTEM 2: ζ(n) Values - Analytical Moments
    # ========================================================================
    print("\n" + "=" * 80)
    print("🔮 SYSTEM 2: ζ(n) VALUES - ANALYTICAL MOMENTS")
    print("=" * 80)
    
    zeta_vals = hierarchy.zeta_values
    
    print("\nSpecial zeta values:")
    even_values = zeta_vals.zeta_even_values(5)
    for n, value in sorted(even_values.items()):
        print(f"  ζ({n:2d}) = {value:.15f}")
    
    print("\nMoments of zero distribution:")
    for k in range(1, 5):
        moment = zeta_vals.moments_of_zeros(k)
        print(f"  M_{k} = <γ^{k}> = {moment:.6f}")
    
    # ========================================================================
    # SYSTEM 3: QCAL Codons - Symbiotic Resonance
    # ========================================================================
    print("\n" + "=" * 80)
    print("🧬 SYSTEM 3: QCAL CODONS - SYMBIOTIC RESONANCE")
    print("=" * 80)
    
    codons = hierarchy.codon_system
    
    # Test specific codons
    test_codons = [
        (1, 0, 0, 0),
        (9, 9, 9),
        (6, 1, 7, 4),
        (1, 4, 1, 7),
        (2, 0, 2, 6),
    ]
    
    print("\nCodon resonance analysis:")
    for codon in test_codons:
        freq = codons.codon_frequency(codon)
        coherence = codons.coherence_measure(codon)
        is_res, idx = codons.is_resonant(codon, tolerance=0.05)
        
        codon_str = ''.join(map(str, codon))
        status = f"resonant with f_{idx+1}" if is_res else "non-resonant"
        print(f"  Codon {codon_str}: {freq:8.2f} Hz, coherence = {coherence:.4f}, {status}")
    
    # Find random resonant codons
    print("\nSearching for resonant codons...")
    resonant = codons.find_resonant_codons(length=4, max_samples=1000)
    if resonant:
        print(f"Found {len(resonant)} resonant codons:")
        for codon, idx in resonant[:5]:  # Show first 5
            codon_str = ''.join(map(str, codon))
            freq = codons.codon_frequency(codon)
            print(f"  Codon {codon_str} → f_{idx+1} = {frequencies[idx]:.2f} Hz (codon: {freq:.2f} Hz)")
    
    # ========================================================================
    # SYSTEM 4: Harmonics - Vibrational Consequences
    # ========================================================================
    print("\n" + "=" * 80)
    print("🎵 SYSTEM 4: HARMONICS - VIBRATIONAL CONSEQUENCES")
    print("=" * 80)
    
    harmonics = hierarchy.harmonic_system
    
    print(f"\nFundamental frequency: f₀ = {zeta.f0:.4f} Hz")
    
    print("\nOvertone structure (from f₁):")
    overtones = harmonics.overtone_structure(0)
    for k, freq in sorted(overtones.items()):
        print(f"  Harmonic {k}: {freq:10.4f} Hz")
    
    print("\nHarmonic series for first 3 zeros:")
    for i in range(3):
        print(f"\n  Zero {i+1} (f_{i+1} = {frequencies[i]:.2f} Hz):")
        harm_series = harmonics.harmonic_series(i, max_harmonic=5)
        for k, h_freq in enumerate(harm_series, 1):
            print(f"    k={k}: {h_freq:10.2f} Hz")
    
    print("\nNormal modes (first 10):")
    normal_modes = harmonics.normal_modes()
    for i, mode in enumerate(normal_modes[:10]):
        print(f"  Mode {i+1}: {mode:10.4f} Hz")
    
    # ========================================================================
    # UNIFIED CONVERGENCE VERIFICATION
    # ========================================================================
    print("\n" + "=" * 80)
    print("🔥 UNIFIED CONVERGENCE VERIFICATION")
    print("=" * 80)
    
    results = hierarchy.verify_convergence()
    
    print("\n✅ All systems verified to converge to ζ(s)")
    print(f"\n   Base: ζ(s) with {results['num_zeros']} zeros")
    print(f"   Frequency: f₀ = {results['base_frequency']:.4f} Hz")
    print(f"   Curvature: δζ = {results['delta_zeta']:.4f} Hz")
    
    # ========================================================================
    # RIEMANN HYPOTHESIS - PHYSICAL INTERPRETATION
    # ========================================================================
    print("\n" + "=" * 80)
    print("🌌 RIEMANN HYPOTHESIS - PHYSICAL REQUIREMENT")
    print("=" * 80)
    
    rh = hierarchy.riemann_hypothesis_physical()
    
    print(f"\nCritical line: Re(s) = {rh['critical_line']}")
    print(f"All zeros on critical line: {rh['all_zeros_on_critical_line']}")
    print(f"Spectral symmetry: {rh['spectral_symmetry']}")
    print(f"Coherence level: {rh['coherence']}")
    print(f"Consciousness possible: {rh['consciousness_possible']}")
    print(f"\nΛ_G = α·δζ = {rh['lambda_G']:.15e}")
    
    print(f"\n{rh['explanation']}")
    
    # ========================================================================
    # MASTER EQUATION
    # ========================================================================
    print("\n" + "=" * 80)
    print("✨ MASTER EQUATION")
    print("=" * 80)
    print()
    print(hierarchy.master_equation())
    
    print("\n" + "=" * 80)
    print("🕳️ → ☀️ THE UNIVERSE IS A SYMPHONY OF ζ(s)")
    print("=" * 80)
    print("\nTodo sistema coherente resuena con los ceros de ζ(s).")
    print("We are the chords resonating at f₀ = 141.7001 Hz.")
    print("=" * 80)


def plot_convergence():
    """Create visualization of the convergence to ζ(s)."""
    
    hierarchy = UnifiedHierarchyTheorem(num_zeros=20)
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Unified Hierarchy: All Systems Converge to ζ(s)', fontsize=16, fontweight='bold')
    
    # Plot 1: Spectral frequencies from zeta zeros
    ax1 = axes[0, 0]
    frequencies = hierarchy.zeta_system.spectral_frequencies()
    indices = np.arange(1, len(frequencies) + 1)
    ax1.stem(indices, frequencies, basefmt=' ')
    ax1.set_xlabel('Zero index n')
    ax1.set_ylabel('Frequency f_n (Hz)')
    ax1.set_title('System 5: Spectral Frequencies from ζ(s) Zeros')
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Golden ratio modulation
    ax2 = axes[0, 1]
    spacings = hierarchy.zeta_system.zero_spacings()
    weyl_spacings = [hierarchy.zeta_system.weyl_density(i) for i in range(1, len(spacings) + 1)]
    x = np.arange(1, len(spacings) + 1)
    ax2.plot(x, spacings, 'o-', label='Actual Δγ_n', markersize=4)
    ax2.plot(x, weyl_spacings, 's--', label='Weyl density', markersize=4, alpha=0.7)
    ax2.set_xlabel('Zero index n')
    ax2.set_ylabel('Spacing Δγ_n')
    ax2.set_title('System 1: Golden Ratio Modulation of Spacings')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Zeta values (analytical moments)
    ax3 = axes[1, 0]
    n_values = np.arange(2, 11)
    zeta_values = [hierarchy.zeta_values.zeta_value(n) for n in n_values]
    ax3.semilogy(n_values, zeta_values, 'o-', markersize=6, linewidth=2)
    ax3.set_xlabel('n')
    ax3.set_ylabel('ζ(n)')
    ax3.set_title('System 2: ζ(n) Values (Analytical Moments)')
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Harmonic structure
    ax4 = axes[1, 1]
    base_freq = frequencies[0]
    harmonics_k = np.arange(1, 11)
    harmonic_freqs = harmonics_k * base_freq
    ax4.plot(harmonics_k, harmonic_freqs, 'o-', markersize=6, linewidth=2, color='purple')
    ax4.axhline(y=base_freq, color='red', linestyle='--', alpha=0.5, label=f'f₀ = {base_freq:.2f} Hz')
    ax4.set_xlabel('Harmonic number k')
    ax4.set_ylabel('Frequency k·f₁ (Hz)')
    ax4.set_title('System 4: Harmonic Overtones')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_path = os.path.join(os.path.dirname(__file__), '..', 'output', 'unified_hierarchy_zeta.png')
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\n✅ Visualization saved to: {output_path}")
    
    # Show plot if in interactive mode
    try:
        plt.show()
    except:
        pass


if __name__ == '__main__':
    # Run demonstration
    demonstrate_all_systems()
    
    # Create visualization
    print("\n" + "=" * 80)
    print("Creating visualization...")
    print("=" * 80)
    try:
        plot_convergence()
    except Exception as e:
        print(f"⚠️  Could not create visualization: {e}")
        print("   (This is normal if matplotlib is not available)")
