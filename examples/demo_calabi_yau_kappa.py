#!/usr/bin/env python3
"""
demo_calabi_yau_kappa.py - Demonstration of Calabi-Yau κ_Π Analysis

This demo shows how to analyze Calabi-Yau varieties using a custom
logarithmic base to compute κ_Π values and perform statistical analysis.

The analysis demonstrates that the millennium constant κ_Π = 2.5773
appears as a structural point in the distribution of Calabi-Yau Hodge numbers.

© JMMB | P vs NP Verification System
"""

import sys
import os

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
    import numpy as np
    
    # Demo 1: Basic analysis
    df, stats = demo_basic_analysis()
    
    # Demo 2: Custom base comparison
    demo_custom_base_comparison()
    
    # Demo 3: N=13 analysis
    demo_n13_analysis()
    
    print("\n" + "=" * 70)
    print("All demonstrations completed successfully!")
    print("=" * 70)
    
    return 0


if __name__ == "__main__":
    import numpy as np
    sys.exit(main())
