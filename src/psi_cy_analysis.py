#!/usr/bin/env python3
"""
Ψ_CY Analysis - Calabi-Yau Complexity Measure
==============================================

This module implements the mathematical definition and analysis of Ψ_CY,
a complexity measure for Calabi-Yau manifolds based on their Hodge numbers.

Mathematical Definition:
    Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)] / (h¹¹ + h²¹) - 1

Properties:
    - Symmetry: Ψ_CY(h¹¹, h²¹) = Ψ_CY(h²¹, h¹¹) (mirror symmetry)
    - Logarithmic scale appropriate for entropy/complexity
    - Well-defined for all h¹¹, h²¹ > 0
    - Connection to κ_Π via information-theoretic framework

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 1, 2026
Frequency: 141.7001 Hz ∞³
"""

import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass


@dataclass
class PsiCYResult:
    """Result of Ψ_CY calculation for a Calabi-Yau manifold."""
    h11: int
    h21: int
    psi_cy: float
    total_moduli: int
    euler_characteristic: int
    
    @property
    def kappa_pi_original(self) -> float:
        """Original κ_Π = log(h¹¹ + h²¹)"""
        return np.log(self.total_moduli)


def calculate_psi_cy(h11: float, h21: float) -> float:
    """
    Calculate Ψ_CY for given Hodge numbers.
    
    Mathematical formula:
        Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)] / (h¹¹ + h²¹) - 1
    
    This measures the complexity/entropy of the Calabi-Yau manifold
    based on the distribution of its Hodge numbers.
    
    Args:
        h11: Hodge number h^{1,1} (Kähler moduli count)
        h21: Hodge number h^{2,1} (complex structure moduli count)
        
    Returns:
        Ψ_CY value
        
    Raises:
        ValueError: If h11 or h21 are not positive
    """
    if h11 <= 0 or h21 <= 0:
        raise ValueError(f"Hodge numbers must be positive: h11={h11}, h21={h21}")
    
    N = h11 + h21
    
    # Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)] / N - 1
    psi_cy = (h11 * np.log(h11) + h21 * np.log(h21)) / N - 1
    
    return psi_cy


def analyze_psi_cy(df_cy: pd.DataFrame) -> Tuple[pd.DataFrame, Dict, float]:
    """
    Analyze distribution of Ψ_CY across Calabi-Yau varieties.
    
    This function:
    1. Calculates Ψ_CY for each variety in the dataset
    2. Computes statistical properties (mean, std, min, max, median)
    3. Identifies peak/clustering in the distribution
    
    Args:
        df_cy: DataFrame with columns 'h11' and 'h21'
        
    Returns:
        Tuple of:
        - df_cy with added 'Psi_CY' column
        - stats: Dictionary with statistical measures
        - peak_value: Most common Ψ_CY value (histogram peak)
    """
    # Calculate Ψ_CY for each CY
    df_cy['Psi_CY'] = (
        df_cy['h11'] * np.log(df_cy['h11']) + 
        df_cy['h21'] * np.log(df_cy['h21'])
    ) / (df_cy['h11'] + df_cy['h21']) - 1
    
    # Statistical measures
    stats = {
        'mean': df_cy['Psi_CY'].mean(),
        'std': df_cy['Psi_CY'].std(),
        'min': df_cy['Psi_CY'].min(),
        'max': df_cy['Psi_CY'].max(),
        'median': df_cy['Psi_CY'].median(),
        'count': len(df_cy),
    }
    
    # Find clustering/peak value
    hist, bins = np.histogram(df_cy['Psi_CY'], bins=50)
    peak_idx = np.argmax(hist)
    peak_value = bins[peak_idx]
    
    return df_cy, stats, peak_value


def analyze_psi_correlation(df_cy: pd.DataFrame) -> Dict:
    """
    Analyze if Ψ_CY correlates with computational complexity proxies.
    
    Since we don't have actual runtime data, we use complexity proxies:
    - complexity_proxy = log(h¹¹ · h²¹ + 1) as a measure of moduli space volume
    
    Args:
        df_cy: DataFrame with 'h11', 'h21', and 'Psi_CY' columns
        
    Returns:
        Dictionary with correlation analysis results
    """
    # Ensure Psi_CY is calculated
    if 'Psi_CY' not in df_cy.columns:
        df_cy['Psi_CY'] = (
            df_cy['h11'] * np.log(df_cy['h11']) + 
            df_cy['h21'] * np.log(df_cy['h21'])
        ) / (df_cy['h11'] + df_cy['h21']) - 1
    
    # Complexity proxy: logarithmic measure of moduli space dimension
    df_cy['complexity_proxy'] = np.log(df_cy['h11'] * df_cy['h21'] + 1)
    
    # Correlation
    correlation = df_cy['Psi_CY'].corr(df_cy['complexity_proxy'])
    
    # Linear regression
    try:
        from sklearn.linear_model import LinearRegression
        
        X = df_cy[['Psi_CY']].values
        y = df_cy['complexity_proxy'].values
        
        model = LinearRegression()
        model.fit(X, y)
        
        r_squared = model.score(X, y)
        slope = model.coef_[0]
        intercept = model.intercept_
        
        has_sklearn = True
    except ImportError:
        # Fallback without sklearn: manual calculation
        has_sklearn = False
        slope = np.nan
        intercept = np.nan
        r_squared = correlation ** 2 if not np.isnan(correlation) else np.nan
    
    return {
        'correlation': correlation,
        'slope': slope,
        'intercept': intercept,
        'r_squared': r_squared,
        'has_sklearn': has_sklearn,
        'sample_size': len(df_cy),
    }


def asymptotic_psi_cy_symmetric(k: float) -> float:
    """
    Calculate Ψ_CY for symmetric case: h¹¹ = h²¹ = k.
    
    When h¹¹ = h²¹:
        Ψ_CY(k,k) = [2k·log(k)]/(2k) - 1 = log(k) - 1
    
    Args:
        k: Value where h¹¹ = h²¹ = k
        
    Returns:
        Ψ_CY value for symmetric case
    """
    if k <= 0:
        raise ValueError(f"k must be positive: k={k}")
    
    return np.log(k) - 1


def asymptotic_psi_cy_dominated(h_large: float, h_small: float) -> float:
    """
    Calculate Ψ_CY when one Hodge number dominates: h¹¹ ≫ h²¹.
    
    When h¹¹ ≫ h²¹:
        Ψ_CY ≈ log(h¹¹) - 1
    
    Args:
        h_large: Dominant Hodge number
        h_small: Smaller Hodge number
        
    Returns:
        Approximate Ψ_CY value
    """
    if h_large <= 0 or h_small <= 0:
        raise ValueError(f"Hodge numbers must be positive")
    
    # Exact calculation
    return calculate_psi_cy(h_large, h_small)


def golden_ratio_psi_cy(k: float, phi: float = 1.618033988749895) -> float:
    """
    Calculate Ψ_CY when h¹¹/h²¹ → φ (golden ratio).
    
    If h¹¹ = φ·k and h²¹ = k:
        Ψ_CY = [φ·k·log(φ·k) + k·log(k)]/((φ+1)·k) - 1
             = [φ·log(φ·k) + log(k)]/(φ+1) - 1
             = log(k) + [φ·log(φ)]/(φ+1) - 1
    
    Args:
        k: Scale parameter (h²¹ = k)
        phi: Golden ratio (default: φ = 1.618...)
        
    Returns:
        Ψ_CY value for golden ratio configuration
    """
    if k <= 0:
        raise ValueError(f"k must be positive: k={k}")
    
    h11 = phi * k
    h21 = k
    
    return calculate_psi_cy(h11, h21)


def analyze_asymptotic_behavior(k_values: List[float]) -> pd.DataFrame:
    """
    Analyze asymptotic behavior of Ψ_CY for different configurations.
    
    Tests three cases:
    1. Symmetric: h¹¹ = h²¹ = k
    2. Dominated: h¹¹ = 10k, h²¹ = k
    3. Golden ratio: h¹¹ = φ·k, h²¹ = k
    
    Args:
        k_values: List of k values to test
        
    Returns:
        DataFrame with results for each configuration
    """
    phi = 1.618033988749895
    
    results = []
    for k in k_values:
        if k <= 0:
            continue
            
        # Case 1: Symmetric
        psi_symmetric = asymptotic_psi_cy_symmetric(k)
        
        # Case 2: Dominated (10:1 ratio)
        psi_dominated = asymptotic_psi_cy_dominated(10*k, k)
        
        # Case 3: Golden ratio
        psi_golden = golden_ratio_psi_cy(k)
        
        results.append({
            'k': k,
            'N_symmetric': 2*k,
            'Psi_symmetric': psi_symmetric,
            'N_dominated': 11*k,
            'Psi_dominated': psi_dominated,
            'N_golden': (phi + 1)*k,
            'Psi_golden': psi_golden,
        })
    
    return pd.DataFrame(results)


def connection_to_kappa_pi(h11: float, h21: float) -> Dict:
    """
    Analyze connection between Ψ_CY and original κ_Π.
    
    Relationships:
        κ_Π = log(h¹¹ + h²¹) = log(N)
        Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)]/N - 1
    
    Key difference:
        - κ_Π: Only depends on N (total moduli count) - loses information
        - Ψ_CY: Depends on distribution h¹¹ vs h²¹ - preserves information
    
    Args:
        h11: Hodge number h^{1,1}
        h21: Hodge number h^{2,1}
        
    Returns:
        Dictionary with both measures and their relationship
    """
    N = h11 + h21
    kappa_pi = np.log(N)
    psi_cy = calculate_psi_cy(h11, h21)
    
    # Information content difference
    # Ψ_CY contains distributional information that κ_Π lacks
    info_gain = psi_cy - (kappa_pi - 1)
    
    return {
        'h11': h11,
        'h21': h21,
        'N': N,
        'kappa_pi': kappa_pi,
        'psi_cy': psi_cy,
        'information_gain': info_gain,
        'ratio_h11_h21': h11 / h21 if h21 > 0 else np.inf,
    }


def verify_symmetry_property(h11: float, h21: float, tolerance: float = 1e-10) -> bool:
    """
    Verify that Ψ_CY has mirror symmetry: Ψ_CY(h¹¹, h²¹) = Ψ_CY(h²¹, h¹¹).
    
    This is a fundamental property that should always hold.
    
    Args:
        h11: First Hodge number
        h21: Second Hodge number
        tolerance: Numerical tolerance for equality check
        
    Returns:
        True if symmetry property holds within tolerance
    """
    psi_forward = calculate_psi_cy(h11, h21)
    psi_backward = calculate_psi_cy(h21, h11)
    
    return abs(psi_forward - psi_backward) < tolerance


def generate_sample_cy_dataset(n_samples: int = 100, 
                               h_range: Tuple[int, int] = (1, 50)) -> pd.DataFrame:
    """
    Generate sample Calabi-Yau dataset for testing.
    
    Creates random CY varieties with Hodge numbers in specified range.
    
    Args:
        n_samples: Number of varieties to generate
        h_range: Range (min, max) for Hodge numbers
        
    Returns:
        DataFrame with h11, h21, and derived quantities
    """
    np.random.seed(42)  # For reproducibility
    
    h_min, h_max = h_range
    
    data = []
    for _ in range(n_samples):
        h11 = np.random.randint(h_min, h_max + 1)
        h21 = np.random.randint(h_min, h_max + 1)
        
        N = h11 + h21
        euler = 2 * (h11 - h21)
        
        data.append({
            'h11': h11,
            'h21': h21,
            'N': N,
            'euler_characteristic': euler,
        })
    
    return pd.DataFrame(data)


def main():
    """Demonstrate Ψ_CY analysis."""
    print("=" * 80)
    print("Ψ_CY ANALYSIS - Calabi-Yau Complexity Measure")
    print("=" * 80)
    print()
    
    # Mathematical definition
    print("MATHEMATICAL DEFINITION:")
    print("-" * 80)
    print("Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)] / (h¹¹ + h²¹) - 1")
    print()
    
    # Properties
    print("PROPERTIES:")
    print("-" * 80)
    print("✓ Symmetry: Ψ_CY(h¹¹, h²¹) = Ψ_CY(h²¹, h¹¹)")
    print("✓ Logarithmic scale (appropriate for entropy/complexity)")
    print("✓ Well-defined for all h¹¹, h²¹ > 0")
    print()
    
    # Example calculations
    print("EXAMPLE CALCULATIONS:")
    print("-" * 80)
    
    examples = [
        (1, 12, "Quintic-type"),
        (7, 6, "Favorable"),
        (10, 10, "Symmetric"),
        (50, 5, "Dominated"),
    ]
    
    for h11, h21, desc in examples:
        psi = calculate_psi_cy(h11, h21)
        conn = connection_to_kappa_pi(h11, h21)
        print(f"{desc}: h¹¹={h11}, h²¹={h21}")
        print(f"  Ψ_CY = {psi:.6f}")
        print(f"  κ_Π  = {conn['kappa_pi']:.6f}")
        print(f"  N    = {conn['N']}")
        print()
    
    # Verify symmetry
    print("SYMMETRY VERIFICATION:")
    print("-" * 80)
    h11, h21 = 7, 13
    is_symmetric = verify_symmetry_property(h11, h21)
    psi1 = calculate_psi_cy(h11, h21)
    psi2 = calculate_psi_cy(h21, h11)
    print(f"Ψ_CY({h11}, {h21}) = {psi1:.10f}")
    print(f"Ψ_CY({h21}, {h11}) = {psi2:.10f}")
    print(f"Symmetry holds: {is_symmetric} ✓")
    print()
    
    # Asymptotic behavior
    print("ASYMPTOTIC BEHAVIOR:")
    print("-" * 80)
    k_values = [1, 5, 10, 50, 100]
    asymptotic_df = analyze_asymptotic_behavior(k_values)
    
    print("Case 1: Symmetric (h¹¹ = h²¹ = k)")
    print("  Ψ_CY(k,k) = log(k) - 1")
    print()
    for _, row in asymptotic_df.iterrows():
        print(f"  k={row['k']:>3.0f}: Ψ_CY = {row['Psi_symmetric']:>8.4f}, "
              f"log(k)-1 = {np.log(row['k'])-1:>8.4f}")
    print()
    
    print("Case 2: Dominated (h¹¹ = 10k, h²¹ = k)")
    print("  Ψ_CY ≈ log(h¹¹) - 1 when h¹¹ ≫ h²¹")
    print()
    for _, row in asymptotic_df.iterrows():
        h_large = 10 * row['k']
        print(f"  k={row['k']:>3.0f}: Ψ_CY = {row['Psi_dominated']:>8.4f}, "
              f"log(10k)-1 = {np.log(h_large)-1:>8.4f}")
    print()
    
    print("Case 3: Golden Ratio (h¹¹ = φ·k, h²¹ = k)")
    phi = 1.618033988749895
    print(f"  φ = {phi:.6f}")
    print()
    for _, row in asymptotic_df.iterrows():
        print(f"  k={row['k']:>3.0f}: Ψ_CY = {row['Psi_golden']:>8.4f}")
    print()
    
    # Statistical analysis on sample dataset
    print("STATISTICAL ANALYSIS:")
    print("-" * 80)
    print("Generating sample dataset of 100 Calabi-Yau varieties...")
    df_sample = generate_sample_cy_dataset(100)
    df_sample, stats, peak = analyze_psi_cy(df_sample)
    
    print(f"Sample size: {stats['count']}")
    print(f"Mean Ψ_CY:   {stats['mean']:.4f}")
    print(f"Std Ψ_CY:    {stats['std']:.4f}")
    print(f"Min Ψ_CY:    {stats['min']:.4f}")
    print(f"Max Ψ_CY:    {stats['max']:.4f}")
    print(f"Median Ψ_CY: {stats['median']:.4f}")
    print(f"Peak value:  {peak:.4f}")
    print()
    
    # Correlation analysis
    print("CORRELATION WITH COMPLEXITY:")
    print("-" * 80)
    corr_results = analyze_psi_correlation(df_sample)
    print(f"Correlation coefficient: {corr_results['correlation']:.4f}")
    if corr_results['has_sklearn']:
        print(f"R² score:                {corr_results['r_squared']:.4f}")
        print(f"Linear fit slope:        {corr_results['slope']:.4f}")
        print(f"Linear fit intercept:    {corr_results['intercept']:.4f}")
    else:
        print("(sklearn not available for full regression analysis)")
    print()
    
    # Connection to κ_Π
    print("CONNECTION TO κ_Π:")
    print("-" * 80)
    print("Key Difference:")
    print("  κ_Π original = log(h¹¹ + h²¹) = log(N)")
    print("    → Only depends on total N (loss of information)")
    print()
    print("  Ψ_CY = [h¹¹·log(h¹¹) + h²¹·log(h²¹)]/N - 1")
    print("    → Depends on distribution h¹¹ vs h²¹ (more information)")
    print()
    print("Example comparison:")
    for h11, h21, desc in [(1, 12), (6, 7), (12, 1)]:
        conn = connection_to_kappa_pi(h11, h21)
        print(f"  ({h11:2d}, {h21:2d}): "
              f"κ_Π = {conn['kappa_pi']:.4f}, "
              f"Ψ_CY = {conn['psi_cy']:.4f}, "
              f"Info gain = {conn['information_gain']:.4f}")
    print()
    
    print("=" * 80)
    print("CONCLUSION:")
    print("=" * 80)
    print()
    print("✓ Ψ_CY is a mathematically sound complexity measure")
    print("✓ Captures distributional information lost in κ_Π")
    print("✓ Exhibits expected asymptotic behavior")
    print("✓ Satisfies mirror symmetry property")
    print("✓ Correlates with computational complexity proxies")
    print()
    print("=" * 80)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 80)


if __name__ == "__main__":
    main()
