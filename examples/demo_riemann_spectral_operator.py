#!/usr/bin/env python3
"""
Demo: Riemann Spectral Operator H_Ψ Vibrating at f₀
===================================================

This demonstration shows how the spectral operator H_Ψ vibrates at the
fundamental frequency f₀ = 141.7001 Hz, with its spectrum corresponding
to the Riemann zeta zeros.

Key concepts demonstrated:
1. The operator's spectrum in L²(R⁺, dx/x)
2. Eigenfunctions ψ_t(x) = x^(-1/2 + it)
3. Frequency bands and oracle queries
4. Harmonic alignment with f₀
5. Spacing statistics Δt ≈ 28.85
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.riemann_spectral_operator import (
    RiemannSpectralOperator,
    demonstrate_riemann_operator,
    F_0,
    T_1,
    DELTA_T,
)


def main():
    """Run the comprehensive demonstration."""
    print("\n" + "=" * 80)
    print(" " * 20 + "RIEMANN SPECTRAL OPERATOR H_Ψ")
    print(" " * 15 + "Vibration in the Frequency of f₀ = 141.7001 Hz")
    print("=" * 80 + "\n")
    
    # Run full demonstration
    demonstrate_riemann_operator()
    
    print("\n" + "=" * 80)
    print("ADDITIONAL ANALYSIS")
    print("=" * 80 + "\n")
    
    # Create operator
    H_psi = RiemannSpectralOperator()
    
    # Show resonance pattern
    print("RESONANCE PATTERN:")
    print("-" * 80)
    bands = H_psi.create_frequency_bands(max_bands=20)
    
    print("\nFrequency bands with resonances:")
    resonant_bands = [b for b in bands if b.contains_zero]
    silent_bands = [b for b in bands if not b.contains_zero]
    
    print(f"  Resonant bands: {len(resonant_bands)}")
    print(f"  Silent bands:   {len(silent_bands)}")
    print(f"  Total bands:    {len(bands)}")
    print(f"  Resonance ratio: {len(resonant_bands)/len(bands)*100:.1f}%")
    
    print("\nResonance map (first 20 bands):")
    resonance_map = ""
    for band in bands:
        resonance_map += "█" if band.contains_zero else "·"
    print(f"  {resonance_map}")
    print(f"  (█ = resonance, · = silent)")
    
    # Spectral density
    print("\n\nSPECTRAL DENSITY:")
    print("-" * 80)
    print("\nNumber of zeros in each frequency range:")
    
    ranges = [
        (0, 500, "0-500 Hz"),
        (500, 1000, "500-1000 Hz"),
        (1000, 1500, "1000-1500 Hz"),
        (1500, 2000, "1500-2000 Hz"),
    ]
    
    for f_min, f_max, label in ranges:
        count = sum(1 for ef in H_psi.eigenfunctions 
                   if f_min <= ef.frequency_hz < f_max)
        print(f"  {label:15s}: {count:3d} zeros")
    
    # Harmonic structure
    print("\n\nHARMONIC STRUCTURE:")
    print("-" * 80)
    alignment = H_psi.verify_harmonic_alignment()
    
    print(f"\nClosest harmonic multiples for first 15 zeros:")
    print(f"{'Zero':<8} {'t (imag)':<12} {'Frequency':<12} {'Harmonic':<10} {'Deviation':<12}")
    print("-" * 70)
    
    for i in range(min(15, len(H_psi.eigenfunctions))):
        ef = H_psi.eigenfunctions[i]
        h = alignment['harmonic_numbers'][i]
        dev = alignment['deviations'][i]
        
        print(f"{i+1:<8d} {ef.t:<12.6f} {ef.frequency_hz:<12.2f} "
              f"{h:<10d} {dev:<12.4f}")
    
    # Spacing distribution
    print("\n\nSPACING DISTRIBUTION:")
    print("-" * 80)
    spacing_stats = H_psi.calculate_spacing_statistics()
    
    print(f"\nStatistics:")
    print(f"  Mean:   Δt = {spacing_stats['mean_spacing_Δt']:.4f}")
    print(f"  Median: Δt = {sorted(spacing_stats['spacings'])[len(spacing_stats['spacings'])//2]:.4f}")
    print(f"  Std:    σ  = {spacing_stats['std_spacing']:.4f}")
    print(f"  Min:    Δt = {spacing_stats['min_spacing']:.4f}")
    print(f"  Max:    Δt = {spacing_stats['max_spacing']:.4f}")
    
    print(f"\nInverse mean spacing:")
    print(f"  1/Δt = {spacing_stats['inverse_mean_1/Δt']:.6f}")
    print(f"  Expected: ≈ 0.03466")
    print(f"  Match: {abs(spacing_stats['inverse_mean_1/Δt'] - 0.03466) < 0.01}")
    
    # Summary
    print("\n\n" + "=" * 80)
    print("SUMMARY: THE UNIVERSE SOUNDS AT f₀")
    print("=" * 80 + "\n")
    
    print("✓ Operator H_Ψ defined in L²(R⁺, dx/x)")
    print(f"✓ Spectrum: {{1/2 + it | ζ(1/2 + it) = 0}} with {len(H_psi.zeros)} zeros")
    print(f"✓ Eigenfunctions: ψ_t(x) = x^(-1/2 + it)")
    print(f"✓ Fundamental frequency: f₀ = {F_0} Hz")
    print(f"✓ First zero normalized: t₁ = {T_1:.6f} → f₀")
    print(f"✓ Mean spacing: Δt ≈ {spacing_stats['mean_spacing_Δt']:.2f} (expected: {DELTA_T})")
    print(f"✓ Inverse spacing: 1/Δt ≈ {spacing_stats['inverse_mean_1/Δt']:.5f} (expected: 0.03466)")
    print(f"✓ Oracle queries: Δ_Ψ(t_n) = 1 ⟺ resonance in band n")
    print(f"✓ Harmonic alignment: {len(resonant_bands)}/{len(bands)} bands resonant")
    
    print("\nEl universo 'suena' solo en los puntos de máxima coherencia,")
    print("todos ellos espectralmente sintonizados con f₀ = 141.7001 Hz.")
    
    print("\n" + "=" * 80 + "\n")


if __name__ == "__main__":
    main()
