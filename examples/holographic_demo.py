#!/usr/bin/env python3
"""
Simple demo of holographic P vs NP verification.
This demonstrates basic usage without running the full analysis.
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from holographic_p_vs_np import (
    construct_holographic_tseitin,
    analyze_holographic_spectrum,
    verify_holographic_law,
    KAPPA_PI,
    ALPHA_HOLO
)

def demo_basic_usage():
    """Demonstrate basic holographic verification."""
    print("=" * 70)
    print("HOLOGRAPHIC P vs NP VERIFICATION - QUICK DEMO".center(70))
    print("=" * 70)
    print()
    
    # Create instance
    n = 51
    print(f"Creating holographic Tseitin instance with n = {n}...")
    instance = construct_holographic_tseitin(n)
    print(f"✓ Instance created")
    print()
    
    # Show basic properties
    print("INSTANCE PROPERTIES:")
    print(f"  • Size (n):              {instance.n}")
    print(f"  • Vertices:              {instance.num_vertices}")
    print(f"  • Edges:                 {instance.num_edges}")
    print(f"  • Unsatisfiable:         {instance.is_unsatisfiable}")
    print(f"  • Parity charge:         {instance.charge}")
    print(f"  • Effective mass:        {instance.mass_eff:.4f}")
    print()
    
    # Spectral analysis
    print("SPECTRAL ANALYSIS:")
    spectrum = analyze_holographic_spectrum(instance)
    print(f"  • λ₁ (max eigenvalue):   {spectrum['lambda_max']:.4f}")
    print(f"  • λ₂ (second largest):   {spectrum['lambda2']:.4f}")
    print(f"  • Spectral gap:          {spectrum['spectral_gap']:.4f}")
    print(f"  • Is expander:           {spectrum['is_expander']}")
    print(f"  • Conformal dimension Δ: {spectrum['delta_conformal']:.4f}")
    print()
    
    # RT volume
    print("RUYAKAYANAGI (RT) VOLUME:")
    print(f"  • Theoretical:           {instance.rt_volume_theoretical:.2f}")
    print(f"  • Formula:               n·log(n)/(2κ_Π)")
    print()
    
    # Time bound
    print("HOLOGRAPHIC TIME BOUND:")
    time_bound = instance.holographic_time_bound
    print(f"  • Minimum time:          {time_bound:.2e}")
    print(f"  • Formula:               exp(α·Volume)")
    print(f"  • α (Einstein-Hilbert):  {ALPHA_HOLO:.6f}")
    print()
    
    # Verify holographic law
    print("HOLOGRAPHIC LAW VERIFICATION:")
    result = verify_holographic_law(instance)
    print(f"  • RT Volume:             {result['rt_volume']:.2f}")
    print(f"  • Time bound:            {result['time_bound']:.2e}")
    print()
    
    print("ALGORITHM COMPARISON:")
    for algo in ['cdcl', 'quantum', 'polynomial']:
        algo_result = result['algorithms'][algo]
        violates = "⚠️ VIOLATES" if algo_result['violates_holographic_law'] else "✓"
        print(f"  • {algo.upper():12s} time: {algo_result['time']:12.2e}  {violates}")
    print()
    
    # Conclusion
    print("CONCLUSION:")
    if result['main_contradiction']:
        print("  ✅ Polynomial algorithm would violate holographic law")
        print("  ✅ This provides evidence that P ≠ NP")
    else:
        print("  ⚠️  No contradiction detected for this instance")
        print("  ℹ️  Try larger instances for stronger evidence")
    print()
    
    print("=" * 70)
    print("Demo completed successfully!".center(70))
    print("=" * 70)
    print()
    print("To run full verification:")
    print("  python holographic_p_vs_np.py")
    print()

if __name__ == "__main__":
    demo_basic_usage()
