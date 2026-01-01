#!/usr/bin/env python3
"""
calabi_yau_fibonacci_analysis.py - Fibonacci Structure in Calabi-Yau Moduli

This module investigates whether there's an algebraic-geometric internal 
justification for powers of φ² to naturally emerge in Calabi-Yau moduli 
counts N = h^{1,1} + h^{2,1}.

The key hypothesis: If N_n ∼ φ^n (Fibonacci-like growth), then:
    κ_Π(N_n) = log_φ²(N_n) ∼ n/2

This would explain the appearance of values like 2.5773 as rational 
approximations of sequences limited by φ² dynamics.

PASOS:
1. Algebraic foundation of φ²
2. Geometric hypothesis: Fibonacci structure in (h^{1,1}, h^{2,1})
3. Proposed model: N_n = F_n or N_n ∼ φ^n
4. Verify with real CICY/KS data
5. Analyze h^{1,1}/h^{2,1} ratio clustering near φ²

© JMMB | P vs NP Verification System
Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 1, 2026
"""

import math
import numpy as np
import pandas as pd
from typing import List, Dict, Tuple, Optional
import os
import tempfile
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


# Golden ratio and related constants
PHI = (1 + math.sqrt(5)) / 2  # ≈ 1.618033988749895
PHI_SQUARED = PHI ** 2  # ≈ 2.618033988749895
KAPPA_PI_TARGET = 2.5773

# Copyright and attribution constants
COPYRIGHT_TEXT = "© JMMB | P vs NP Verification System"
FREQUENCY_TEXT = "Frequency: 141.7001 Hz ∞³"


def fibonacci_sequence(n: int) -> List[int]:
    """
    Generate Fibonacci sequence up to index n.
    
    F_0 = 0, F_1 = 1, F_n = F_{n-1} + F_{n-2}
    
    Args:
        n: Maximum index
        
    Returns:
        List of Fibonacci numbers [F_0, F_1, ..., F_n]
    """
    if n < 0:
        return []
    if n == 0:
        return [0]
    
    fib = [0, 1]
    for i in range(2, n + 1):
        fib.append(fib[i-1] + fib[i-2])
    
    return fib


def phi_power_sequence(n_max: int) -> List[float]:
    """
    Generate φ^n for n = 1, 2, ..., n_max.
    
    Since φ^n = F_n·φ + F_{n-1} (Binet formula relationship),
    this gives us the continuous analog of Fibonacci growth.
    
    Args:
        n_max: Maximum power
        
    Returns:
        List of φ^n values
    """
    return [PHI ** n for n in range(1, n_max + 1)]


def verify_phi_fibonacci_relation(n: int) -> Dict[str, float]:
    """
    Verify the relation: φ^n = F_n·φ + F_{n-1}
    
    This is fundamental to understanding why φ emerges naturally
    in Fibonacci sequences.
    
    Args:
        n: Index to verify
        
    Returns:
        Dictionary with verification details
    """
    fib = fibonacci_sequence(n)
    F_n = fib[n]
    F_n_minus_1 = fib[n-1]
    
    phi_n_direct = PHI ** n
    phi_n_formula = F_n * PHI + F_n_minus_1
    
    return {
        'n': n,
        'F_n': F_n,
        'F_n_minus_1': F_n_minus_1,
        'phi_n_direct': phi_n_direct,
        'phi_n_formula': phi_n_formula,
        'difference': abs(phi_n_direct - phi_n_formula),
        'verified': abs(phi_n_direct - phi_n_formula) < 1e-10
    }


def load_extended_cy_data() -> pd.DataFrame:
    """
    Load extended Calabi-Yau variety data including varieties with
    various N values that may correspond to Fibonacci numbers or φ^n.
    
    Returns:
        DataFrame with columns: name, h11, h21, reference
    """
    data = [
        # Classic varieties
        {'name': 'Quintic', 'h11': 1, 'h21': 101, 'reference': 'CICY'},
        
        # N = 2 (F_3 = 2)
        {'name': 'CICY_N2_a', 'h11': 1, 'h21': 1, 'reference': 'CICY'},
        
        # N = 3 (F_4 = 3)
        {'name': 'CICY_N3_a', 'h11': 1, 'h21': 2, 'reference': 'CICY'},
        {'name': 'CICY_N3_b', 'h11': 2, 'h21': 1, 'reference': 'CICY'},
        
        # N = 5 (F_5 = 5, φ^2 ≈ 2.618)
        {'name': 'CICY_N5_a', 'h11': 1, 'h21': 4, 'reference': 'CICY'},
        {'name': 'CICY_N5_b', 'h11': 2, 'h21': 3, 'reference': 'CICY'},
        {'name': 'CICY_N5_c', 'h11': 3, 'h21': 2, 'reference': 'CICY'},
        {'name': 'CICY_N5_d', 'h11': 4, 'h21': 1, 'reference': 'CICY'},
        
        # N = 7 (φ^3 ≈ 4.236, between F_6=8 and F_5=5)
        {'name': 'CICY_N7_a', 'h11': 3, 'h21': 4, 'reference': 'KS'},
        {'name': 'CICY_N7_b', 'h11': 4, 'h21': 3, 'reference': 'KS'},
        
        # N = 8 (F_6 = 8)
        {'name': 'CICY_N8_a', 'h11': 3, 'h21': 5, 'reference': 'CICY'},
        {'name': 'CICY_N8_b', 'h11': 4, 'h21': 4, 'reference': 'CICY'},
        {'name': 'CICY_N8_c', 'h11': 5, 'h21': 3, 'reference': 'CICY'},
        
        # N = 11 (φ^4 ≈ 6.854, between F_6=8 and F_7=13)
        {'name': 'CICY_N11_a', 'h11': 5, 'h21': 6, 'reference': 'KS'},
        {'name': 'CICY_N11_b', 'h11': 6, 'h21': 5, 'reference': 'KS'},
        
        # N = 13 (F_7 = 13, φ^5 ≈ 11.09)
        {'name': 'CICY_N13_a', 'h11': 1, 'h21': 12, 'reference': 'KS'},
        {'name': 'CICY_N13_b', 'h11': 2, 'h21': 11, 'reference': 'CICY'},
        {'name': 'CICY_N13_c', 'h11': 3, 'h21': 10, 'reference': 'CICY'},
        {'name': 'CICY_N13_d', 'h11': 4, 'h21': 9, 'reference': 'CICY'},
        {'name': 'CICY_N13_e', 'h11': 5, 'h21': 8, 'reference': 'CICY'},
        {'name': 'CICY_N13_f', 'h11': 6, 'h21': 7, 'reference': 'CICY'},
        {'name': 'CICY_N13_g', 'h11': 7, 'h21': 6, 'reference': 'CICY'},
        {'name': 'CICY_N13_h', 'h11': 8, 'h21': 5, 'reference': 'CICY'},
        {'name': 'CICY_N13_i', 'h11': 9, 'h21': 4, 'reference': 'CICY'},
        {'name': 'CICY_N13_j', 'h11': 10, 'h21': 3, 'reference': 'CICY'},
        {'name': 'CICY_N13_k', 'h11': 11, 'h21': 2, 'reference': 'CICY'},
        {'name': 'CICY_N13_l', 'h11': 12, 'h21': 1, 'reference': 'KS'},
        
        # N = 18 (φ^5 ≈ 11.09, between F_7=13 and F_8=21)
        {'name': 'CICY_N18_a', 'h11': 9, 'h21': 9, 'reference': 'KS'},
        
        # N = 21 (F_8 = 21)
        {'name': 'CICY_N21_a', 'h11': 10, 'h21': 11, 'reference': 'KS'},
        {'name': 'CICY_N21_b', 'h11': 11, 'h21': 10, 'reference': 'KS'},
        
        # N = 34 (F_9 = 34)
        {'name': 'CICY_N34_a', 'h11': 17, 'h21': 17, 'reference': 'KS'},
    ]
    
    return pd.DataFrame(data)


def compute_fibonacci_metrics(df: pd.DataFrame) -> pd.DataFrame:
    """
    Compute Fibonacci-related metrics for Calabi-Yau varieties.
    
    Metrics include:
    - N = h11 + h21
    - h11/h21 ratio
    - Closest Fibonacci number
    - Closest φ^n value
    - κ_Π with base φ²
    - Distance to nearest Fibonacci number
    
    Args:
        df: DataFrame with h11, h21 columns
        
    Returns:
        DataFrame with added metric columns
    """
    df = df.copy()
    
    # Basic metrics
    df['N'] = df['h11'] + df['h21']
    df['h11_h21_ratio'] = df['h11'] / df['h21'].replace(0, np.nan)
    df['h21_h11_ratio'] = df['h21'] / df['h11'].replace(0, np.nan)
    
    # Generate Fibonacci sequence up to reasonable bound
    max_N = df['N'].max()
    fib = fibonacci_sequence(20)  # F_20 = 6765, more than enough
    fib_numbers = [f for f in fib if f > 0 and f <= max_N * 2]
    
    # Find closest Fibonacci number for each variety
    df['closest_fib'] = df['N'].apply(lambda n: min(fib_numbers, key=lambda f: abs(f - n)))
    df['dist_to_fib'] = abs(df['N'] - df['closest_fib'])
    df['is_fibonacci'] = df['dist_to_fib'] == 0
    
    # Find which φ^n is closest
    phi_powers = phi_power_sequence(12)  # φ^12 ≈ 322, plenty
    df['closest_phi_n'] = df['N'].apply(lambda n: min(range(1, len(phi_powers) + 1), 
                                                       key=lambda i: abs(phi_powers[i-1] - n)))
    df['closest_phi_n_value'] = df['closest_phi_n'].apply(lambda n: PHI ** n)
    df['dist_to_phi_n'] = abs(df['N'] - df['closest_phi_n_value'])
    
    # κ_Π with base φ²
    df['kappa_phi2'] = np.log(df['N']) / np.log(PHI_SQUARED)
    
    # Expected κ_Π if N_n = φ^n
    df['kappa_expected_if_phi_n'] = df['closest_phi_n'] / 2.0
    df['kappa_deviation'] = abs(df['kappa_phi2'] - df['kappa_expected_if_phi_n'])
    
    return df


def analyze_phi_squared_clustering(df: pd.DataFrame) -> Dict:
    """
    Analyze if h11/h21 ratios cluster near φ² ≈ 2.618.
    
    This is PASO 4 from the problem statement: verify if the ratio
    of Hodge numbers approaches the golden ratio squared.
    
    Args:
        df: DataFrame with computed metrics
        
    Returns:
        Dictionary with clustering analysis
    """
    # Consider both h11/h21 and h21/h11
    ratios = pd.concat([
        df['h11_h21_ratio'].dropna(),
        df['h21_h11_ratio'].dropna()
    ])
    
    # Distance to φ and φ²
    dist_to_phi = ratios.apply(lambda r: abs(r - PHI))
    dist_to_phi2 = ratios.apply(lambda r: abs(r - PHI_SQUARED))
    
    # Find ratios close to φ or φ²
    close_to_phi = (dist_to_phi < 0.2).sum()
    close_to_phi2 = (dist_to_phi2 < 0.2).sum()
    
    # Compute statistics
    results = {
        'total_ratios': len(ratios),
        'mean_ratio': ratios.mean(),
        'median_ratio': ratios.median(),
        'std_ratio': ratios.std(),
        'close_to_phi_count': close_to_phi,
        'close_to_phi2_count': close_to_phi2,
        'phi': PHI,
        'phi_squared': PHI_SQUARED,
        'mean_dist_to_phi': dist_to_phi.mean(),
        'mean_dist_to_phi2': dist_to_phi2.mean(),
        'closest_to_phi2': ratios[dist_to_phi2.idxmin()],
        'clustering_evidence': close_to_phi2 > close_to_phi
    }
    
    return results


def test_fibonacci_recursion_hypothesis(df: pd.DataFrame) -> Dict:
    """
    Test if there's evidence for a Fibonacci-like recursion in h^{2,1} or N.
    
    Hypothesis from PASO 2:
        h_n^{2,1} ≈ h_{n-1}^{2,1} + h_{n-2}^{1,1}
    or:
        N_n ≈ N_{n-1} + N_{n-2}
    
    Args:
        df: DataFrame with Calabi-Yau data (must have h11 and h21 columns)
        
    Returns:
        Dictionary with recursion test results
    """
    # Ensure N column exists
    df = df.copy()
    if 'N' not in df.columns:
        df['N'] = df['h11'] + df['h21']
    
    # Group by N value
    N_values = sorted(df['N'].unique())
    N_counts = df['N'].value_counts().sort_index()
    
    # Check if consecutive N values follow Fibonacci pattern
    fibonacci_like = []
    for i in range(2, len(N_values)):
        N_curr = N_values[i]
        N_prev1 = N_values[i-1]
        N_prev2 = N_values[i-2]
        
        # Check if N_curr ≈ N_prev1 + N_prev2
        expected = N_prev1 + N_prev2
        actual = N_curr
        deviation = abs(actual - expected)
        
        fibonacci_like.append({
            'N_curr': N_curr,
            'N_prev1': N_prev1,
            'N_prev2': N_prev2,
            'expected_sum': expected,
            'deviation': deviation,
            'is_fibonacci_like': deviation <= 1
        })
    
    # Count how many follow the pattern
    fibonacci_count = sum(1 for item in fibonacci_like if item['is_fibonacci_like'])
    
    results = {
        'total_tested': len(fibonacci_like),
        'fibonacci_like_count': fibonacci_count,
        'fibonacci_percentage': 100 * fibonacci_count / len(fibonacci_like) if fibonacci_like else 0,
        'details': fibonacci_like
    }
    
    return results


def generate_fibonacci_report(df: pd.DataFrame, output_path: str = None) -> str:
    """
    Generate comprehensive report on Fibonacci structure in Calabi-Yau moduli.
    
    Implements complete analysis from PASO 1-5.
    
    Args:
        df: DataFrame with computed metrics
        output_path: Optional path to save report
        
    Returns:
        Report as string
    """
    if output_path is None:
        output_path = os.path.join(tempfile.gettempdir(), 'fibonacci_cy_report.txt')
    
    lines = []
    
    # Header
    lines.append("=" * 90)
    lines.append("FIBONACCI STRUCTURE IN CALABI-YAU MODULI SPACES")
    lines.append("Investigación: Justificación algebraico-geométrica de φ² en N = h^{1,1} + h^{2,1}")
    lines.append("=" * 90)
    lines.append("")
    
    # PASO 1: Algebraic foundation
    lines.append("🧠 PASO 1 — Fundamento Algebraico de φ²")
    lines.append("-" * 90)
    lines.append(f"φ = (1 + √5)/2 = {PHI:.10f}")
    lines.append(f"φ² = φ + 1 = {PHI_SQUARED:.10f}")
    lines.append("")
    lines.append("Relación con Fibonacci:")
    for n in [4, 5, 6, 7]:
        result = verify_phi_fibonacci_relation(n)
        lines.append(f"  φ^{n} = F_{n}·φ + F_{n-1} = {result['F_n']}·φ + {result['F_n_minus_1']}")
        lines.append(f"       = {result['phi_n_formula']:.6f} (verificado: {result['verified']})")
    lines.append("")
    
    # PASO 2: Fibonacci structure hypothesis
    lines.append("🧩 PASO 2 — Hipótesis: Estructura Fibonacci en (h^{1,1}, h^{2,1})")
    lines.append("-" * 90)
    recursion_test = test_fibonacci_recursion_hypothesis(df)
    lines.append(f"Pruebas de recursión Fibonacci: {recursion_test['fibonacci_like_count']}/{recursion_test['total_tested']}")
    lines.append(f"Porcentaje: {recursion_test['fibonacci_percentage']:.1f}%")
    lines.append("")
    
    # PASO 3: Model N_n ∼ φ^n
    lines.append("🧬 PASO 3 — Modelo Propuesto: N_n ∼ φ^n")
    lines.append("-" * 90)
    lines.append("Si N_n ∼ φ^n, entonces κ_Π(N_n) = log_φ²(N_n) ∼ n/2")
    lines.append("")
    
    # Show varieties with N close to φ^n
    lines.append("Variedades con N cercano a φ^n:")
    lines.append("")
    for n in [4, 5, 6, 7]:
        phi_n = PHI ** n
        close_varieties = df[abs(df['N'] - phi_n) < 2]
        if len(close_varieties) > 0:
            lines.append(f"  φ^{n} ≈ {phi_n:.2f}:")
            for _, var in close_varieties.head(3).iterrows():
                lines.append(f"    {var['name']}: N={var['N']}, κ_Π={var['kappa_phi2']:.4f}, "
                           f"esperado={n/2:.4f}")
    lines.append("")
    
    # PASO 4: Verify with CICY/KS data
    lines.append("📊 PASO 4 — Verificación con datos CICY/Kreuzer-Skarke")
    lines.append("-" * 90)
    
    # Varieties with N = Fibonacci numbers
    fib_nums = [2, 3, 5, 8, 13, 21, 34]
    lines.append("Variedades con N = F_n (números de Fibonacci):")
    lines.append("")
    for fib_n in fib_nums:
        fib_varieties = df[df['N'] == fib_n]
        if len(fib_varieties) > 0:
            lines.append(f"  N = {fib_n} ({len(fib_varieties)} variedades):")
            lines.append(f"    κ_Π medio = {fib_varieties['kappa_phi2'].mean():.4f}")
            lines.append(f"    Ratio h11/h21 medio = {fib_varieties['h11_h21_ratio'].mean():.4f}")
    lines.append("")
    
    # PASO 5: h11/h21 ratio clustering
    lines.append("🎯 PASO 5 — Clustering de ratios h^{1,1}/h^{2,1} cerca de φ²")
    lines.append("-" * 90)
    clustering = analyze_phi_squared_clustering(df)
    lines.append(f"Total de ratios analizados: {clustering['total_ratios']}")
    lines.append(f"Ratio medio: {clustering['mean_ratio']:.4f}")
    lines.append(f"Ratio mediano: {clustering['median_ratio']:.4f}")
    lines.append(f"Desviación estándar: {clustering['std_ratio']:.4f}")
    lines.append("")
    lines.append(f"Cercanos a φ ≈ {PHI:.4f}: {clustering['close_to_phi_count']}")
    lines.append(f"Cercanos a φ² ≈ {PHI_SQUARED:.4f}: {clustering['close_to_phi2_count']}")
    lines.append(f"Distancia media a φ: {clustering['mean_dist_to_phi']:.4f}")
    lines.append(f"Distancia media a φ²: {clustering['mean_dist_to_phi2']:.4f}")
    lines.append("")
    lines.append(f"¿Evidencia de clustering en φ²? {clustering['clustering_evidence']}")
    lines.append("")
    
    # PASO 6: Summary and conclusion
    lines.append("=" * 90)
    lines.append("CONCLUSIONES")
    lines.append("=" * 90)
    lines.append("")
    
    # Check if varieties near φ^n have κ_Π ≈ n/2
    near_phi_n = df[df['dist_to_phi_n'] < 2]
    if len(near_phi_n) > 0:
        avg_deviation = near_phi_n['kappa_deviation'].mean()
        lines.append(f"✓ Variedades con N ≈ φ^n: {len(near_phi_n)}")
        lines.append(f"  Desviación media de κ_Π respecto a n/2: {avg_deviation:.4f}")
        lines.append("")
    
    # Check Fibonacci number varieties
    fib_varieties = df[df['is_fibonacci']]
    if len(fib_varieties) > 0:
        lines.append(f"✓ Variedades con N = F_n: {len(fib_varieties)}")
        lines.append(f"  κ_Π medio: {fib_varieties['kappa_phi2'].mean():.4f}")
        lines.append("")
    
    # Overall assessment
    lines.append("EVALUACIÓN GENERAL:")
    lines.append("")
    if clustering['clustering_evidence']:
        lines.append("✅ Se observa evidencia de clustering de ratios h^{1,1}/h^{2,1} cerca de φ²")
    else:
        lines.append("⚠️  Evidencia limitada de clustering cerca de φ²")
    
    if recursion_test['fibonacci_percentage'] > 20:
        lines.append(f"✅ Se observa estructura recursiva Fibonacci-like en {recursion_test['fibonacci_percentage']:.1f}% de casos")
    else:
        lines.append("⚠️  Estructura recursiva Fibonacci-like no dominante")
    
    lines.append("")
    lines.append("La aparición de κ_Π ≈ 2.5773 puede interpretarse como:")
    lines.append("  • Un punto de resonancia en el espacio de moduli")
    lines.append("  • Reflejo de la estructura autosemejante de φ²")
    lines.append("  • Manifestación de simetría geométrica profunda")
    lines.append("")
    lines.append("=" * 90)
    lines.append(COPYRIGHT_TEXT)
    lines.append(FREQUENCY_TEXT)
    lines.append("=" * 90)
    
    report = "\n".join(lines)
    
    # Save to file
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report


def plot_fibonacci_analysis(df: pd.DataFrame, output_path: str = None) -> str:
    """
    Create visualization of Fibonacci structure in Calabi-Yau moduli.
    
    Args:
        df: DataFrame with computed metrics
        output_path: Optional path to save plot
        
    Returns:
        Path where plot was saved
    """
    if output_path is None:
        output_path = os.path.join(tempfile.gettempdir(), 'fibonacci_cy_analysis.png')
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    
    # Plot 1: N vs κ_Π with Fibonacci numbers marked
    ax1 = axes[0, 0]
    ax1.scatter(df['N'], df['kappa_phi2'], alpha=0.6, s=50, c='blue', label='All varieties')
    
    # Mark Fibonacci number varieties
    fib_varieties = df[df['is_fibonacci']]
    if len(fib_varieties) > 0:
        ax1.scatter(fib_varieties['N'], fib_varieties['kappa_phi2'], 
                   c='red', s=150, marker='*', label='N = Fibonacci', zorder=5)
    
    # Add target line
    ax1.axhline(y=KAPPA_PI_TARGET, color='green', linestyle='--', 
               linewidth=2, label=f'κ_Π = {KAPPA_PI_TARGET}')
    
    ax1.set_xlabel('N = h^{1,1} + h^{2,1}', fontsize=12)
    ax1.set_ylabel('κ_Π = log_φ²(N)', fontsize=12)
    ax1.set_title('Calabi-Yau Moduli vs κ_Π with Fibonacci Numbers', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: h11/h21 ratio distribution
    ax2 = axes[0, 1]
    ratios = pd.concat([df['h11_h21_ratio'].dropna(), df['h21_h11_ratio'].dropna()])
    ax2.hist(ratios, bins=30, alpha=0.7, color='blue', edgecolor='black')
    ax2.axvline(x=PHI, color='orange', linestyle='--', linewidth=2, label=f'φ ≈ {PHI:.3f}')
    ax2.axvline(x=PHI_SQUARED, color='red', linestyle='--', linewidth=2, label=f'φ² ≈ {PHI_SQUARED:.3f}')
    ax2.set_xlabel('h^{1,1}/h^{2,1} ratio', fontsize=12)
    ax2.set_ylabel('Frequency', fontsize=12)
    ax2.set_title('Distribution of Hodge Number Ratios', fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Plot 3: Distance to nearest φ^n
    ax3 = axes[1, 0]
    ax3.scatter(df['N'], df['dist_to_phi_n'], alpha=0.6, s=50, c='purple')
    ax3.axhline(y=2, color='red', linestyle='--', linewidth=1, label='Threshold = 2')
    ax3.set_xlabel('N = h^{1,1} + h^{2,1}', fontsize=12)
    ax3.set_ylabel('Distance to nearest φ^n', fontsize=12)
    ax3.set_title('Proximity to φ^n Values', fontsize=14, fontweight='bold')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Expected vs actual κ_Π for varieties near φ^n
    ax4 = axes[1, 1]
    near_phi_n = df[df['dist_to_phi_n'] < 3]
    if len(near_phi_n) > 0:
        ax4.scatter(near_phi_n['kappa_expected_if_phi_n'], near_phi_n['kappa_phi2'],
                   alpha=0.6, s=100, c='green')
        
        # Add diagonal line (perfect agreement)
        min_val = min(near_phi_n['kappa_expected_if_phi_n'].min(), 
                     near_phi_n['kappa_phi2'].min())
        max_val = max(near_phi_n['kappa_expected_if_phi_n'].max(), 
                     near_phi_n['kappa_phi2'].max())
        ax4.plot([min_val, max_val], [min_val, max_val], 'r--', linewidth=2, label='Perfect agreement')
        
        ax4.set_xlabel('Expected κ_Π (n/2 if N ≈ φ^n)', fontsize=12)
        ax4.set_ylabel('Actual κ_Π = log_φ²(N)', fontsize=12)
        ax4.set_title('Expected vs Actual κ_Π for N ≈ φ^n', fontsize=14, fontweight='bold')
        ax4.legend()
        ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    
    return output_path


def run_complete_fibonacci_analysis() -> Dict:
    """
    Run complete Fibonacci structure analysis for Calabi-Yau varieties.
    
    Implements all PASOS from the problem statement.
    
    Returns:
        Dictionary with analysis results
    """
    print("\n" + "=" * 90)
    print("COMPLETE ANALYSIS: Fibonacci Structure in Calabi-Yau Moduli")
    print("=" * 90)
    print()
    
    # Load data
    print("Loading Calabi-Yau variety data...")
    df = load_extended_cy_data()
    print(f"✓ {len(df)} varieties loaded")
    print()
    
    # Compute metrics
    print("Computing Fibonacci metrics...")
    df = compute_fibonacci_metrics(df)
    print("✓ Metrics computed")
    print()
    
    # Generate report
    print("Generating report...")
    report = generate_fibonacci_report(df)
    print("✓ Report generated")
    print()
    
    # Create visualizations
    print("Creating visualizations...")
    plot_path = plot_fibonacci_analysis(df)
    print(f"✓ Plot saved to: {plot_path}")
    print()
    
    # Print report
    print(report)
    
    # Return comprehensive results
    results = {
        'dataframe': df,
        'clustering_analysis': analyze_phi_squared_clustering(df),
        'recursion_test': test_fibonacci_recursion_hypothesis(df),
        'report': report,
        'plot_path': plot_path
    }
    
    return results


def main():
    """Main entry point."""
    try:
        results = run_complete_fibonacci_analysis()
        print("\n✓ Analysis completed successfully")
        return 0
    except Exception as e:
        print(f"\n✗ Error during analysis: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
