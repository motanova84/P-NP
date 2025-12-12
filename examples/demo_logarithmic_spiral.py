"""
Demonstration of Logarithmic Spiral and Field Ψ
================================================

This script demonstrates and visualizes the logarithmic spiral and field Ψ
implementations, showing the connection with κ_Π.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import cmath
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import matplotlib.patches as mpatches

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from logarithmic_spiral import (
    z_spiral, spiral_magnitude, psi_field, effective_area,
    R_MIN, R_MAX, R_THRESHOLD, C0, ALPHA,
    validate_spiral_properties, validate_field_properties
)
from constants import KAPPA_PI, GOLDEN_RATIO


def plot_logarithmic_spiral():
    """Plot the logarithmic spiral and mark κ_Π points."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # Generate spiral points
    theta_max = 3 * 2 * math.pi  # 3 complete turns
    theta_vals = np.linspace(0, theta_max, 500)
    
    # Compute spiral in Cartesian coordinates
    z_vals = [z_spiral(theta) for theta in theta_vals]
    x_vals = [z.real for z in z_vals]
    y_vals = [z.imag for z in z_vals]
    
    # Plot 1: Spiral in complex plane
    ax1.plot(x_vals, y_vals, 'b-', linewidth=2, label='Logarithmic Spiral')
    
    # Mark κ_Π points at each complete turn
    for n in range(4):
        theta_n = n * 2 * math.pi
        z_n = z_spiral(theta_n)
        if n > 0:
            ax1.plot(z_n.real, z_n.imag, 'ro', markersize=10, 
                    label=f'Turn {n}: |z| = κ_Π^{n} = {abs(z_n):.3f}')
    
    ax1.set_xlabel('Real', fontsize=12)
    ax1.set_ylabel('Imaginary', fontsize=12)
    ax1.set_title('Logarithmic Spiral z(θ) = exp(θ(c₀ + i))', fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.axis('equal')
    ax1.legend(loc='best', fontsize=9)
    
    # Plot 2: Magnitude vs angle
    magnitudes = [abs(z) for z in z_vals]
    turns = theta_vals / (2 * math.pi)
    
    ax2.plot(turns, magnitudes, 'b-', linewidth=2, label='|z(θ)|')
    
    # Mark κ_Π^n points
    for n in range(1, 4):
        theta_n = n * 2 * math.pi
        mag_n = spiral_magnitude(theta_n)
        ax2.plot(n, mag_n, 'ro', markersize=10, label=f'κ_Π^{n} = {mag_n:.3f}')
    
    ax2.axhline(y=KAPPA_PI, color='r', linestyle='--', alpha=0.5, label=f'κ_Π = {KAPPA_PI}')
    ax2.set_xlabel('Number of Turns', fontsize=12)
    ax2.set_ylabel('Magnitude |z(θ)|', fontsize=12)
    ax2.set_title(f'Spiral Magnitude Growth (c₀ = {C0:.4f})', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(loc='best', fontsize=9)
    
    plt.tight_layout()
    plt.savefig('/tmp/logarithmic_spiral.png', dpi=150, bbox_inches='tight')
    print("Saved spiral plot to /tmp/logarithmic_spiral.png")
    plt.close()


def plot_field_psi():
    """Plot the field Ψ in the ring region."""
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 12))
    
    # Create grid for field visualization
    r_vals = np.linspace(R_MIN, R_MAX, 100)
    theta_vals = np.linspace(0, 2*math.pi, 100)
    R, Theta = np.meshgrid(r_vals, theta_vals)
    
    # Compute field magnitude
    Psi_mag = np.zeros_like(R)
    for i in range(R.shape[0]):
        for j in range(R.shape[1]):
            try:
                Psi_mag[i, j] = abs(psi_field(R[i, j], Theta[i, j]))
            except:
                Psi_mag[i, j] = 0
    
    # Plot 1: Field magnitude in polar coordinates
    ax1 = plt.subplot(2, 2, 1, projection='polar')
    contour1 = ax1.contourf(Theta, R, Psi_mag, levels=20, cmap='viridis')
    ax1.set_title('Field Magnitude |Ψ(r, θ)|', fontsize=12, fontweight='bold', pad=20)
    plt.colorbar(contour1, ax=ax1, label='|Ψ|')
    
    # Plot 2: Radial decay profile
    theta_fixed = 0
    mag_profile = [abs(psi_field(r, theta_fixed)) for r in r_vals]
    
    ax2.plot(r_vals, mag_profile, 'b-', linewidth=2, label=f'|Ψ(r, θ={theta_fixed})|')
    ax2.axvline(x=R_THRESHOLD, color='r', linestyle='--', label=f'Threshold r = {R_THRESHOLD}')
    ax2.set_xlabel('Radius r', fontsize=11)
    ax2.set_ylabel('Field Magnitude |Ψ|', fontsize=11)
    ax2.set_title(f'Radial Decay (α = 1/κ_Π = {ALPHA:.4f})', fontsize=12, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=9)
    
    # Plot 3: Effective area
    a_eff_vals = [effective_area(r) for r in r_vals]
    
    ax3.plot(r_vals, a_eff_vals, 'g-', linewidth=2, label='A_eff(r)')
    ax3.axvline(x=R_THRESHOLD, color='r', linestyle='--', label=f'Threshold r = {R_THRESHOLD}')
    ax3.axhline(y=1.0/KAPPA_PI, color='orange', linestyle='--', 
               label=f'1/κ_Π = {1.0/KAPPA_PI:.4f}')
    
    # Mark threshold value
    a_eff_thresh = effective_area(R_THRESHOLD)
    ax3.plot(R_THRESHOLD, a_eff_thresh, 'ro', markersize=10,
            label=f'A_eff({R_THRESHOLD:.1f}) = {a_eff_thresh:.3f}')
    
    ax3.set_xlabel('Radius r', fontsize=11)
    ax3.set_ylabel('Effective Area A_eff(r)', fontsize=11)
    ax3.set_title('Coherence: A_eff(r) = 1.054 × (1/r)^α', fontsize=12, fontweight='bold')
    ax3.grid(True, alpha=0.3)
    ax3.legend(fontsize=9)
    
    # Plot 4: Field phase
    phase_profile = []
    r_sample = r_vals[::5]  # Sample every 5th point for efficiency
    
    for r in r_sample:
        psi = psi_field(r, theta_fixed)
        phase = cmath.phase(psi)
        phase_profile.append(phase)
    
    ax4.scatter(r_sample, phase_profile, c=r_sample, cmap='plasma', s=50)
    ax4.axvline(x=R_THRESHOLD, color='r', linestyle='--', label=f'Threshold r = {R_THRESHOLD}')
    ax4.set_xlabel('Radius r', fontsize=11)
    ax4.set_ylabel('Phase (radians)', fontsize=11)
    ax4.set_title('Field Phase Structure', fontsize=12, fontweight='bold')
    ax4.grid(True, alpha=0.3)
    ax4.legend(fontsize=9)
    
    plt.tight_layout()
    plt.savefig('/tmp/field_psi.png', dpi=150, bbox_inches='tight')
    print("Saved field plot to /tmp/field_psi.png")
    plt.close()


def plot_coherence_analysis():
    """Plot coherence analysis showing the relationship between structures."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # Plot 1: Compare spiral magnitude with field magnitude
    theta_vals = np.linspace(0, 2*math.pi, 100)
    
    # Spiral magnitude at various turns
    spiral_mags_1 = [spiral_magnitude(theta) for theta in theta_vals]
    spiral_mags_2 = [spiral_magnitude(theta + 2*math.pi) for theta in theta_vals]
    
    ax1.plot(np.degrees(theta_vals), spiral_mags_1, 'b-', linewidth=2, label='Spiral Turn 1')
    ax1.plot(np.degrees(theta_vals), spiral_mags_2, 'g-', linewidth=2, label='Spiral Turn 2')
    ax1.axhline(y=KAPPA_PI, color='r', linestyle='--', linewidth=2, label=f'κ_Π = {KAPPA_PI}')
    
    ax1.set_xlabel('Angle θ (degrees)', fontsize=11)
    ax1.set_ylabel('Magnitude', fontsize=11)
    ax1.set_title('Spiral Growth Toward κ_Π', fontsize=12, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=10)
    
    # Plot 2: Unified scaling analysis
    r_vals = np.linspace(R_MIN, R_MAX, 100)
    
    # Different scaling relationships
    field_scaling = [abs(psi_field(r, 0)) for r in r_vals]
    a_eff_scaling = [effective_area(r) for r in r_vals]
    
    # Normalize for comparison
    field_norm = [f / max(field_scaling) for f in field_scaling]
    a_eff_norm = [a / max(a_eff_scaling) for a in a_eff_scaling]
    
    ax2.plot(r_vals, field_norm, 'b-', linewidth=2, label='|Ψ| (normalized)')
    ax2.plot(r_vals, a_eff_norm, 'g--', linewidth=2, label='A_eff (normalized)')
    ax2.axvline(x=R_THRESHOLD, color='r', linestyle='--', 
               label=f'Threshold = {R_THRESHOLD}')
    
    # Mark coherence point
    idx_thresh = np.argmin(np.abs(r_vals - R_THRESHOLD))
    ax2.plot(R_THRESHOLD, field_norm[idx_thresh], 'ro', markersize=10,
            label='Coherence Point')
    
    ax2.set_xlabel('Radius r', fontsize=11)
    ax2.set_ylabel('Normalized Value', fontsize=11)
    ax2.set_title('Unified Scaling with κ_Π', fontsize=12, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=10)
    
    plt.tight_layout()
    plt.savefig('/tmp/coherence_analysis.png', dpi=150, bbox_inches='tight')
    print("Saved coherence analysis to /tmp/coherence_analysis.png")
    plt.close()


def print_summary():
    """Print summary of calculations and validations."""
    print("=" * 70)
    print("LOGARITHMIC SPIRAL AND FIELD Ψ - DEMONSTRATION")
    print("=" * 70)
    print()
    
    print("FUNDAMENTAL CONSTANTS:")
    print("-" * 70)
    print(f"  κ_Π (Millennium Constant): {KAPPA_PI}")
    print(f"  Golden Ratio φ: {GOLDEN_RATIO:.6f}")
    print(f"  c₀ = log(κ_Π)/(2π): {C0:.6f}")
    print(f"  α = 1/κ_Π: {ALPHA:.6f}")
    print(f"  Threshold r = {R_THRESHOLD} (upper bound of ring)")
    print()
    
    print("SPIRAL VALIDATION:")
    print("-" * 70)
    spiral_results = validate_spiral_properties()
    print(f"  One turn: |z(2π)| = {spiral_results['one_turn_actual']:.6f}")
    print(f"  Expected: κ_Π = {KAPPA_PI}")
    print(f"  Valid: {spiral_results['one_turn_valid']}")
    print()
    print(f"  Three turns: |z(6π)| = {spiral_results['three_turns_actual']:.6f}")
    print(f"  Expected: κ_Π³ = {spiral_results['three_turns_expected']:.6f}")
    print(f"  Valid: {spiral_results['three_turns_valid']}")
    print()
    
    print("FIELD Ψ VALIDATION:")
    print("-" * 70)
    field_results = validate_field_properties()
    print(f"  α (decay factor): {field_results['alpha']:.6f}")
    print(f"  β (angular freq): {field_results['beta']:.6f}")
    print(f"  γ (torsion): {field_results['gamma']:.6f}")
    print()
    print(f"  At threshold r = {R_THRESHOLD}:")
    print(f"    A_eff({R_THRESHOLD}) = {field_results['threshold_a_eff']:.6f}")
    print(f"    1/κ_Π = {field_results['expected_ratio']:.6f}")
    print(f"    Coherent: {field_results['is_coherent']}")
    print()
    
    print("KEY RELATIONSHIPS:")
    print("-" * 70)
    print("  1. Spiral passes through κ_Π at each complete turn (θ = 2πn)")
    print(f"     z(θ) = exp(θ(c₀ + i)) where c₀ = log(κ_Π)/(2π)")
    print()
    print("  2. Field decays with radius in the ring (1 ≤ r ≤ 4):")
    print(f"     Ψ(r,θ) = Ψ₀ × r^(-α) × exp(i(βθ + γlog(r)))")
    print(f"     where α = 1/κ_Π ≈ {ALPHA:.4f}")
    print()
    print("  3. Effective area shows coherence at threshold:")
    print(f"     A_eff(r) = 1.054 × (1/r)^α")
    print(f"     A_eff({R_THRESHOLD}) ≈ {effective_area(R_THRESHOLD):.3f}")
    print(f"     Compare with 1/κ_Π ≈ {1.0/KAPPA_PI:.3f}")
    print()
    
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)


def main():
    """Main demonstration function."""
    print("\nGenerating visualizations...\n")
    
    # Print summary
    print_summary()
    print()
    
    # Generate plots
    print("Creating plots...")
    plot_logarithmic_spiral()
    plot_field_psi()
    plot_coherence_analysis()
    
    print()
    print("=" * 70)
    print("All visualizations generated successfully!")
    print("=" * 70)
    print()
    print("Generated files:")
    print("  - /tmp/logarithmic_spiral.png")
    print("  - /tmp/field_psi.png")
    print("  - /tmp/coherence_analysis.png")
    print()


if __name__ == "__main__":
    main()
