#!/usr/bin/env python3
"""
Demo script for Calabi-Yau varieties dataset.

This demonstrates how to use the Calabi-Yau varieties dataset
for complexity analysis.

© JMMB | P vs NP Verification System
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_complexity import CalabiYauComplexity

def main():
    """Main demonstration."""
    print("=" * 70)
    print("Calabi-Yau Varieties Dataset Demonstration")
    print("=" * 70)
    print()
    
    # Initialize the complexity analyzer
    cy = CalabiYauComplexity()
    
    # Get all varieties
    varieties = cy.get_all_varieties()
    print(f"Loaded {len(varieties)} Calabi-Yau varieties from the dataset")
    print()
    
    # Display each variety
    print("All Varieties:")
    print("-" * 70)
    for variety in varieties:
        print(f"{variety['id']}: {variety['nombre']}")
        print(f"  Hodge numbers: h11={variety['h11']}, h21={variety['h21']}")
        print(f"  Geometric parameters: α={variety['alpha']}, β={variety['beta']}")
        print(f"  Spectral entropy: κ_Π={variety['kappa_pi']}")
        print(f"  Euler characteristic: χ={variety['chi_euler']}")
        print()
    
    # Analyze a specific variety
    print("-" * 70)
    print("Detailed Analysis: Quíntica ℂℙ⁴[5]")
    print("-" * 70)
    quintica = cy.get_variety('CY-001')
    if quintica:
        metrics = cy.compute_variety_complexity(quintica, n_vars=200)
        print(f"Variety: {metrics['variety_name']}")
        print(f"  ID: {metrics['variety_id']}")
        print(f"  Hodge numbers: h11={metrics['h11']}, h21={metrics['h21']}")
        print(f"  Euler characteristic: χ={metrics['chi_euler']}")
        print(f"  α={metrics['alpha']}, β={metrics['beta']}")
        print(f"  Spectral entropy (κ_Π): {metrics['kappa_pi']}")
        print(f"  Holographic complexity (n=200): {metrics['holographic_complexity']:.4f}")
    print()
    
    # Statistical analysis
    print("-" * 70)
    print("Statistical Analysis of Dataset")
    print("-" * 70)
    stats = cy.analyze_varieties_dataset()
    print(f"Total varieties: {stats['count']}")
    print()
    print(f"h11 (Hodge number):")
    print(f"  Range: [{stats['h11']['min']}, {stats['h11']['max']}]")
    print(f"  Mean: {stats['h11']['mean']:.2f} ± {stats['h11']['std']:.2f}")
    print()
    print(f"h21 (Hodge number):")
    print(f"  Range: [{stats['h21']['min']}, {stats['h21']['max']}]")
    print(f"  Mean: {stats['h21']['mean']:.2f} ± {stats['h21']['std']:.2f}")
    print()
    print(f"α (geometric parameter):")
    print(f"  Range: [{stats['alpha']['min']:.3f}, {stats['alpha']['max']:.3f}]")
    print(f"  Mean: {stats['alpha']['mean']:.3f} ± {stats['alpha']['std']:.3f}")
    print()
    print(f"β (geometric parameter):")
    print(f"  Range: [{stats['beta']['min']:.3f}, {stats['beta']['max']:.3f}]")
    print(f"  Mean: {stats['beta']['mean']:.3f} ± {stats['beta']['std']:.3f}")
    print()
    print(f"κ_Π (spectral entropy):")
    print(f"  Range: [{stats['kappa_pi']['min']:.5f}, {stats['kappa_pi']['max']:.5f}]")
    print(f"  Mean: {stats['kappa_pi']['mean']:.5f} ± {stats['kappa_pi']['std']:.5f}")
    print()
    print(f"χ (Euler characteristic):")
    print(f"  Range: [{stats['chi_euler']['min']}, {stats['chi_euler']['max']}]")
    print(f"  Mean: {stats['chi_euler']['mean']:.2f} ± {stats['chi_euler']['std']:.2f}")
    print()
    
    print("=" * 70)
    print("✅ Demo completed successfully!")
    print("=" * 70)
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
