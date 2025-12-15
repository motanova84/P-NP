#!/usr/bin/env python3
"""
Advanced 3D Visualizations for Frequency-Dependent Complexity
==============================================================

This module provides advanced visualization capabilities for the three-dimensional
complexity analysis framework: Space × Time × Frequency

Features:
- 3D surface plots of complexity landscapes
- Frequency sweep visualizations
- Comparative analysis plots
- Interactive visualizations

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import math
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import matplotlib.cm as cm
from typing import List, Tuple, Optional

from constants import (
    OMEGA_CRITICAL,
    KAPPA_PI,
    spectral_constant_at_frequency,
    information_complexity_at_frequency,
    spectral_sweep_analysis,
    analyze_three_dimensional_complexity,
)


def plot_3d_complexity_landscape(
    num_vars_range: Tuple[int, int] = (10, 100),
    treewidth_range: Tuple[int, int] = (5, 50),
    omega: float = OMEGA_CRITICAL,
    resolution: int = 20,
    save_path: Optional[str] = None
) -> None:
    """
    Create a 3D surface plot of the complexity landscape.
    
    Plots Space (n) × Topology (tw) × Time (IC) at a fixed frequency.
    
    Args:
        num_vars_range: Range of variable counts (min, max)
        treewidth_range: Range of treewidth values (min, max)
        omega: Frequency at which to analyze (default: critical)
        resolution: Number of points per axis
        save_path: Optional path to save the figure
    """
    # Create mesh grid
    n_values = np.linspace(num_vars_range[0], num_vars_range[1], resolution)
    tw_values = np.linspace(treewidth_range[0], treewidth_range[1], resolution)
    N, TW = np.meshgrid(n_values, tw_values)
    
    # Calculate IC for each point
    IC = np.zeros_like(N)
    for i in range(resolution):
        for j in range(resolution):
            n = int(N[i, j])
            tw = TW[i, j]
            IC[i, j] = information_complexity_at_frequency(tw, n, omega)
    
    # Create 3D plot
    fig = plt.figure(figsize=(12, 8))
    ax = fig.add_subplot(111, projection='3d')
    
    # Surface plot
    surf = ax.plot_surface(N, TW, IC, cmap=cm.viridis, alpha=0.8,
                          linewidth=0, antialiased=True)
    
    # Labels
    ax.set_xlabel('Space (n variables)', fontsize=10)
    ax.set_ylabel('Topology (treewidth)', fontsize=10)
    ax.set_zlabel('Time (IC bits)', fontsize=10)
    
    # Title
    freq_label = f"ω = {omega:.2f} Hz"
    if abs(omega) < 1e-6:
        freq_label = "ω = 0 (classical)"
    elif abs(omega - OMEGA_CRITICAL) < 1e-6:
        freq_label = f"ω = ω_c = {OMEGA_CRITICAL} Hz (critical)"
    
    ax.set_title(f'3D Complexity Landscape\n{freq_label}', fontsize=12, pad=20)
    
    # Color bar
    fig.colorbar(surf, ax=ax, shrink=0.5, aspect=5, label='IC (bits)')
    
    # Adjust viewing angle
    ax.view_init(elev=25, azim=45)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved 3D complexity landscape to {save_path}")
    else:
        plt.show()
    
    plt.close()


def plot_frequency_sweep_2d(
    num_vars: int = 100,
    treewidth: float = 50,
    frequency_range: Tuple[float, float] = (0.0, 200.0),
    num_points: int = 100,
    save_path: Optional[str] = None
) -> None:
    """
    Plot how IC varies across frequencies for a fixed problem.
    
    Args:
        num_vars: Number of variables
        treewidth: Treewidth of the problem
        frequency_range: Range of frequencies to sweep (min, max) in Hz
        num_points: Number of frequency points to sample
        save_path: Optional path to save the figure
    """
    # Generate frequency sweep
    frequencies = np.linspace(frequency_range[0], frequency_range[1], num_points)
    sweep_results = spectral_sweep_analysis(num_vars, treewidth, frequencies.tolist())
    
    # Extract data
    omegas = [r['frequency_omega'] for r in sweep_results]
    ics = [r['time_ic_bits'] for r in sweep_results]
    kappas = [r['kappa_at_frequency'] for r in sweep_results]
    
    # Create plot with two y-axes
    fig, ax1 = plt.subplots(figsize=(12, 6))
    
    # IC on left axis
    color = 'tab:blue'
    ax1.set_xlabel('Frequency ω (Hz)', fontsize=11)
    ax1.set_ylabel('Information Complexity (bits)', color=color, fontsize=11)
    line1 = ax1.plot(omegas, ics, color=color, linewidth=2, label='IC(ω)')
    ax1.tick_params(axis='y', labelcolor=color)
    ax1.grid(True, alpha=0.3)
    
    # κ_Π on right axis
    ax2 = ax1.twinx()
    color = 'tab:red'
    ax2.set_ylabel('Spectral Constant κ_Π(ω)', color=color, fontsize=11)
    line2 = ax2.plot(omegas, kappas, color=color, linewidth=2, 
                     linestyle='--', label='κ_Π(ω)')
    ax2.tick_params(axis='y', labelcolor=color)
    
    # Mark critical frequency
    ax1.axvline(x=OMEGA_CRITICAL, color='green', linestyle=':', 
                linewidth=2, alpha=0.7, label=f'ω_c = {OMEGA_CRITICAL} Hz')
    
    # Title and legend
    plt.title(f'Frequency Sweep Analysis\nn = {num_vars} variables, tw = {treewidth}', 
              fontsize=12, pad=15)
    
    # Combine legends
    lines = line1 + line2 + [plt.Line2D([0], [0], color='green', 
                                         linestyle=':', linewidth=2)]
    labels = ['IC(ω)', 'κ_Π(ω)', f'ω_c = {OMEGA_CRITICAL} Hz']
    ax1.legend(lines, labels, loc='upper left', fontsize=10)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved frequency sweep plot to {save_path}")
    else:
        plt.show()
    
    plt.close()


def plot_3d_space_time_frequency(
    num_vars: int = 100,
    treewidth_range: Tuple[float, float] = (5, 50),
    frequency_range: Tuple[float, float] = (0.0, 200.0),
    resolution: int = 30,
    save_path: Optional[str] = None
) -> None:
    """
    Create a 3D visualization of Time × Frequency × Topology.
    
    For a fixed space dimension (n), shows how IC varies with
    both treewidth and frequency.
    
    Args:
        num_vars: Fixed number of variables
        treewidth_range: Range of treewidth values (min, max)
        frequency_range: Range of frequencies (min, max) in Hz
        resolution: Number of points per axis
        save_path: Optional path to save the figure
    """
    # Create mesh grid
    tw_values = np.linspace(treewidth_range[0], treewidth_range[1], resolution)
    omega_values = np.linspace(frequency_range[0], frequency_range[1], resolution)
    TW, OMEGA = np.meshgrid(tw_values, omega_values)
    
    # Calculate IC for each point
    IC = np.zeros_like(TW)
    for i in range(resolution):
        for j in range(resolution):
            tw = TW[i, j]
            omega = OMEGA[i, j]
            IC[i, j] = information_complexity_at_frequency(tw, num_vars, omega)
    
    # Create 3D plot
    fig = plt.figure(figsize=(12, 8))
    ax = fig.add_subplot(111, projection='3d')
    
    # Surface plot
    surf = ax.plot_surface(TW, OMEGA, IC, cmap=cm.plasma, alpha=0.9,
                          linewidth=0, antialiased=True)
    
    # Labels
    ax.set_xlabel('Topology (treewidth)', fontsize=10)
    ax.set_ylabel('Frequency ω (Hz)', fontsize=10)
    ax.set_zlabel('Time (IC bits)', fontsize=10)
    
    # Title
    ax.set_title(f'3D: Time × Frequency × Topology\nSpace: n = {num_vars} variables', 
                fontsize=12, pad=20)
    
    # Color bar
    fig.colorbar(surf, ax=ax, shrink=0.5, aspect=5, label='IC (bits)')
    
    # Mark critical frequency plane
    # Create a semi-transparent plane at ω_c
    tw_plane = np.linspace(treewidth_range[0], treewidth_range[1], 2)
    ic_plane = np.linspace(0, np.max(IC), 2)
    TW_plane, IC_plane = np.meshgrid(tw_plane, ic_plane)
    OMEGA_plane = np.ones_like(TW_plane) * OMEGA_CRITICAL
    ax.plot_surface(TW_plane, OMEGA_plane, IC_plane, alpha=0.2, color='green')
    
    # Adjust viewing angle
    ax.view_init(elev=20, azim=135)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved 3D space-time-frequency plot to {save_path}")
    else:
        plt.show()
    
    plt.close()


def plot_comparison_classical_vs_critical(
    num_vars_range: Tuple[int, int] = (10, 100),
    treewidth_ratio: float = 0.5,
    num_points: int = 20,
    save_path: Optional[str] = None
) -> None:
    """
    Compare IC at classical vs critical frequency as problem size varies.
    
    Args:
        num_vars_range: Range of variable counts (min, max)
        treewidth_ratio: Ratio of treewidth to n
        num_points: Number of points to sample
        save_path: Optional path to save the figure
    """
    n_values = np.linspace(num_vars_range[0], num_vars_range[1], num_points, dtype=int)
    
    ic_classical = []
    ic_critical = []
    kappa_classical = []
    kappa_critical = []
    
    for n in n_values:
        tw = int(n * treewidth_ratio)
        if tw < 1:
            tw = 1
        
        # Classical frequency
        ic_classical.append(information_complexity_at_frequency(tw, n, 0.0))
        kappa_classical.append(spectral_constant_at_frequency(0.0, n))
        
        # Critical frequency
        ic_critical.append(information_complexity_at_frequency(tw, n, OMEGA_CRITICAL))
        kappa_critical.append(spectral_constant_at_frequency(OMEGA_CRITICAL, n))
    
    # Create subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Plot 1: IC comparison
    ax1.plot(n_values, ic_classical, 'b-o', linewidth=2, markersize=4, 
            label='ω = 0 (classical)')
    ax1.plot(n_values, ic_critical, 'r-s', linewidth=2, markersize=4, 
            label=f'ω = {OMEGA_CRITICAL} Hz (critical)')
    ax1.set_xlabel('Problem Size (n variables)', fontsize=11)
    ax1.set_ylabel('Information Complexity (bits)', fontsize=11)
    ax1.set_title('IC: Classical vs Critical Frequency', fontsize=12)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: κ_Π decay
    ax2.plot(n_values, kappa_classical, 'b-o', linewidth=2, markersize=4, 
            label='ω = 0 (classical)')
    ax2.plot(n_values, kappa_critical, 'r-s', linewidth=2, markersize=4, 
            label=f'ω = {OMEGA_CRITICAL} Hz (critical)')
    ax2.set_xlabel('Problem Size (n variables)', fontsize=11)
    ax2.set_ylabel('Spectral Constant κ_Π(ω)', fontsize=11)
    ax2.set_title('κ_Π Decay at Critical Frequency', fontsize=12)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.set_yscale('log')
    
    plt.suptitle(f'Classical vs Critical Regime Comparison\nTreewidth = {treewidth_ratio}×n', 
                fontsize=13, y=1.02)
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved comparison plot to {save_path}")
    else:
        plt.show()
    
    plt.close()


def plot_complexity_amplification_heatmap(
    num_vars_range: Tuple[int, int] = (10, 100),
    treewidth_range: Tuple[int, int] = (5, 50),
    resolution: int = 20,
    save_path: Optional[str] = None
) -> None:
    """
    Create a heatmap showing IC amplification from classical to critical frequency.
    
    Args:
        num_vars_range: Range of variable counts (min, max)
        treewidth_range: Range of treewidth values (min, max)
        resolution: Number of points per axis
        save_path: Optional path to save the figure
    """
    # Create mesh grid
    n_values = np.linspace(num_vars_range[0], num_vars_range[1], resolution, dtype=int)
    tw_values = np.linspace(treewidth_range[0], treewidth_range[1], resolution)
    
    # Calculate amplification ratios
    amplification = np.zeros((resolution, resolution))
    for i, n in enumerate(n_values):
        for j, tw in enumerate(tw_values):
            ic_classical = information_complexity_at_frequency(tw, n, 0.0)
            ic_critical = information_complexity_at_frequency(tw, n, OMEGA_CRITICAL)
            if ic_classical > 0:
                amplification[j, i] = ic_critical / ic_classical
            else:
                amplification[j, i] = 1.0
    
    # Create heatmap
    fig, ax = plt.subplots(figsize=(10, 8))
    
    im = ax.imshow(amplification, cmap='hot', aspect='auto', origin='lower',
                   extent=[num_vars_range[0], num_vars_range[1], 
                          treewidth_range[0], treewidth_range[1]])
    
    ax.set_xlabel('Problem Size (n variables)', fontsize=11)
    ax.set_ylabel('Treewidth', fontsize=11)
    ax.set_title('Complexity Amplification: IC(ω_c) / IC(0)\nFrom Classical to Critical Frequency', 
                fontsize=12, pad=15)
    
    # Color bar
    cbar = plt.colorbar(im, ax=ax, label='Amplification Factor')
    
    # Add contour lines
    contours = ax.contour(n_values, tw_values, amplification, colors='white', 
                         alpha=0.4, linewidths=1)
    ax.clabel(contours, inline=True, fontsize=8)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved amplification heatmap to {save_path}")
    else:
        plt.show()
    
    plt.close()


def create_all_visualizations(output_dir: str = "./output/visualizations") -> None:
    """
    Generate all visualization types and save to output directory.
    
    Args:
        output_dir: Directory to save all visualization files
    """
    import os
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating 3D complexity visualizations...")
    print("=" * 70)
    
    # 1. 3D complexity landscape at classical frequency
    print("1. Creating 3D complexity landscape (classical)...")
    plot_3d_complexity_landscape(
        omega=0.0,
        save_path=f"{output_dir}/3d_landscape_classical.png"
    )
    
    # 2. 3D complexity landscape at critical frequency
    print("2. Creating 3D complexity landscape (critical)...")
    plot_3d_complexity_landscape(
        omega=OMEGA_CRITICAL,
        save_path=f"{output_dir}/3d_landscape_critical.png"
    )
    
    # 3. Frequency sweep
    print("3. Creating frequency sweep plot...")
    plot_frequency_sweep_2d(
        save_path=f"{output_dir}/frequency_sweep.png"
    )
    
    # 4. 3D time-frequency-topology
    print("4. Creating 3D time-frequency-topology plot...")
    plot_3d_space_time_frequency(
        save_path=f"{output_dir}/3d_time_frequency_topology.png"
    )
    
    # 5. Classical vs critical comparison
    print("5. Creating classical vs critical comparison...")
    plot_comparison_classical_vs_critical(
        save_path=f"{output_dir}/comparison_classical_critical.png"
    )
    
    # 6. Amplification heatmap
    print("6. Creating complexity amplification heatmap...")
    plot_complexity_amplification_heatmap(
        save_path=f"{output_dir}/amplification_heatmap.png"
    )
    
    print("=" * 70)
    print(f"All visualizations saved to {output_dir}/")
    print("=" * 70)


if __name__ == "__main__":
    print("=" * 70)
    print("Advanced 3D Visualizations for Frequency-Dependent Complexity")
    print("=" * 70)
    print()
    
    # Create all visualizations
    create_all_visualizations()
    
    print()
    print("Visualization examples:")
    print("-" * 70)
    print("1. 3D Complexity Landscapes: Space × Topology × Time")
    print("   - Shows how IC varies with problem size and treewidth")
    print("   - Available at classical (ω=0) and critical (ω=ω_c) frequencies")
    print()
    print("2. Frequency Sweep: Shows IC and κ_Π variation across ω")
    print("   - Identifies critical frequencies and phase transitions")
    print("   - Dual y-axis plot for IC and κ_Π")
    print()
    print("3. 3D Time-Frequency-Topology: Complete three-dimensional view")
    print("   - Fixed problem size, varies treewidth and frequency")
    print("   - Shows activation at critical frequency")
    print()
    print("4. Classical vs Critical Comparison")
    print("   - Direct comparison of both regimes")
    print("   - Shows κ_Π decay and IC amplification")
    print()
    print("5. Amplification Heatmap")
    print("   - Shows IC(ω_c) / IC(0) ratio across parameter space")
    print("   - Identifies regions of maximum complexity amplification")
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
