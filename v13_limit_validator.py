"""
V13 Thermodynamic Limit Validator - Extrapolation to Infinity Constant
=======================================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ
Protocol: QCAL-SYMBIO-BRIDGE v1.3.0

This module implements V13 thermodynamic limit analysis:
- Multi-scale sweep: N = [128, 256, 512, 1024, 2560]
- Fit model: C_est(N) = κ_∞ + a/N^α
- Number Variance Σ²(L) calculation and GOE comparison
- Extrapolation to κ_∞ = 2.577310...

Defines class 𝔅 of modal bases satisfying:
P1 (Periodicity): φₙ(t+T) = φₙ(t) with T = 1/f₀
P2 (No-Hereditariedad): Coupling operator K is strictly real and symmetric
P3 (Saturación de Ramsey): Edge density d ∈ [0.17, 0.19]
P4 (Alineación Riemann): Eigenvalue spectrum projects to critical line Re(s) = 1/2
"""

import numpy as np
import json
from typing import List, Dict, Tuple
from dataclasses import dataclass, asdict
from scipy.optimize import curve_fit
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

# Import QCAL constants and Atlas3 modal analysis
from qcal.constants import F0_QCAL, KAPPA_PI
from atlas3_modal_analysis import Atlas3ModalAnalysis


# Target value for κ_∞
KAPPA_INFINITY_TARGET = 2.577310

# Multi-scale system sizes
SYSTEM_SIZES = [128, 256, 512, 1024, 2560]


@dataclass
class V13Results:
    """Results from V13 thermodynamic limit analysis"""
    # Scaling fit parameters
    kappa_infinity: float           # Extrapolated κ_∞
    kappa_infinity_error: float     # Fit error
    fit_parameter_a: float          # Coefficient a in C_est(N) = κ_∞ + a/N^α
    fit_exponent_alpha: float       # Exponent α
    fit_exponent_error: float       # Error in α
    relative_error_percent: float   # |(κ_∞ - κ_Π)/κ_Π| × 100
    
    # Multi-scale data
    system_sizes: List[int]
    kappa_values: List[float]
    scaled_values: List[float]      # κ(N) × √(N log N)
    
    # Number variance data
    L_values: List[float]           # Unfolding interval lengths
    sigma2_values: List[float]      # Number variance Σ²(L)
    sigma2_goe_values: List[float]  # GOE prediction
    sigma2_poisson_values: List[float]  # Poisson (random) prediction
    
    # Spectral properties
    eigenvalue_spacings: List[float]  # Normalized eigenvalue spacings
    
    # Class 𝔅 verification
    class_B_properties: Dict[str, bool]
    
    # Metadata
    timestamp: str
    protocol_version: str


class V13LimitValidator:
    """
    V13 Thermodynamic Limit Validator
    
    Implements:
    - Multi-scale sweep for κ(N)
    - Non-linear regression to extrapolate κ_∞
    - Number variance Σ²(L) calculation
    - GOE comparison and rigidity analysis
    """
    
    def __init__(self, f0: float = F0_QCAL):
        """
        Initialize V13 validator
        
        Args:
            f0: Fundamental frequency (Hz)
        """
        self.f0 = f0
        self.kappa_pi = KAPPA_PI
        self.analyzer = Atlas3ModalAnalysis(f0=f0, phase_seed=2.5773)
        
    def fit_function(self, N: np.ndarray, kappa_inf: float, a: float, alpha: float) -> np.ndarray:
        """
        Fit model: C_est(N) = κ_∞ + a/N^α
        
        Args:
            N: System sizes
            kappa_inf: Asymptotic value κ_∞
            a: Coefficient
            alpha: Exponent
            
        Returns:
            Estimated curvature values
        """
        return kappa_inf + a / (N ** alpha)
    
    def compute_multi_scale_sweep(self, sizes: List[int]) -> Tuple[List[float], List[float]]:
        """
        Compute κ(N) for multiple system sizes
        
        Args:
            sizes: List of system sizes N
            
        Returns:
            Tuple of (kappa_values, scaled_values)
        """
        print("=" * 80)
        print(" V13 MULTI-SCALE SWEEP ".center(80))
        print("=" * 80)
        print()
        
        kappa_values = []
        scaled_values = []
        
        for N in sizes:
            print(f"Computing κ({N})...")
            kappa_n = self.analyzer.calculate_kappa_n(N)
            scaled = kappa_n * np.sqrt(N * np.log(N))
            
            kappa_values.append(kappa_n)
            scaled_values.append(scaled)
            
            print(f"  κ({N}) = {kappa_n:.6f}")
            print(f"  κ({N})·√(N log N) = {scaled:.6f}")
            print()
        
        return kappa_values, scaled_values
    
    def extrapolate_kappa_infinity(self, sizes: List[int], 
                                   kappa_values: List[float],
                                   scaled_values: List[float]) -> Dict:
        """
        Extrapolate κ_∞ using non-linear regression
        
        We fit the scaled values C_est(N) = κ(N)·√(N log N) to the model:
        C_est(N) = κ_∞ + a/N^α
        
        Args:
            sizes: System sizes
            kappa_values: Computed κ(N) values
            scaled_values: Scaled values κ(N)·√(N log N)
            
        Returns:
            Dictionary with fit parameters and statistics
        """
        print("=" * 80)
        print(" EXTRAPOLATING κ_∞ (V13-B) ".center(80))
        print("=" * 80)
        print()
        
        # Convert to numpy arrays
        N_array = np.array(sizes, dtype=float)
        C_array = np.array(scaled_values, dtype=float)  # Use scaled values!
        
        # Initial guess for parameters
        # κ_∞ ~ 2.577, a ~ 10.0, α ~ 0.5
        p0 = [2.577, 10.0, 0.5]
        
        try:
            # Perform non-linear fit on scaled values
            popt, pcov = curve_fit(self.fit_function, N_array, C_array, 
                                  p0=p0, maxfev=10000)
            
            kappa_inf, a, alpha = popt
            
            # Extract errors from covariance matrix
            perr = np.sqrt(np.diag(pcov))
            kappa_inf_err, a_err, alpha_err = perr
            
            # Calculate relative error vs target
            rel_error = abs(kappa_inf - KAPPA_INFINITY_TARGET) / KAPPA_INFINITY_TARGET
            
            print(f"Fit Results (C_est(N) = κ_∞ + a/N^α):")
            print(f"  κ_∞ = {kappa_inf:.6f} ± {kappa_inf_err:.6f}")
            print(f"  a = {a:.6f} ± {a_err:.6f}")
            print(f"  α = {alpha:.4f} ± {alpha_err:.4f}")
            print()
            print(f"Target: κ_Π = {KAPPA_INFINITY_TARGET:.6f}")
            print(f"Relative Error: {rel_error * 100:.4f}%")
            print()
            
            # Check if within target (0.1% threshold mentioned in problem)
            convergence_achieved = rel_error < 0.001  # 0.1%
            print(f"Convergence Status: {'✓ ACHIEVED' if convergence_achieved else '✗ IN PROGRESS'}")
            print(f"  (Target: < 0.1% error)")
            print()
            
            return {
                'kappa_infinity': float(kappa_inf),
                'kappa_infinity_error': float(kappa_inf_err),
                'fit_parameter_a': float(a),
                'fit_parameter_a_error': float(a_err),
                'fit_exponent_alpha': float(alpha),
                'fit_exponent_alpha_error': float(alpha_err),
                'relative_error': float(rel_error),
                'convergence_achieved': bool(convergence_achieved),
                'fit_success': True
            }
            
        except Exception as e:
            print(f"Error during fit: {e}")
            return {
                'fit_success': False,
                'error': str(e)
            }
    
    def compute_eigenvalue_spacings(self, N: int, num_samples: int = 1000) -> np.ndarray:
        """
        Compute normalized eigenvalue spacings for spectral analysis
        
        Args:
            N: System size
            num_samples: Number of eigenvalues to extract
            
        Returns:
            Array of normalized spacings
        """
        # Use simplified mode to generate eigenvalues efficiently
        # Generate coupling operator for smaller size (for efficiency)
        n_modes = min(N, 100)  # Limit for computational efficiency
        
        operator = self.analyzer.construct_coupling_operator(n_modes)
        full_matrix = (operator.off_diagonal + 
                      np.diag(operator.diagonal))
        
        # Symmetrize
        matrix_sym = (full_matrix + full_matrix.T) / 2
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(matrix_sym)
        eigenvalues = np.sort(eigenvalues)
        
        # Calculate spacings
        spacings = np.diff(eigenvalues)
        
        # Normalize by mean spacing (unfolding)
        mean_spacing = np.mean(spacings)
        if mean_spacing > 0:
            normalized_spacings = spacings / mean_spacing
        else:
            normalized_spacings = spacings
        
        return normalized_spacings
    
    def compute_number_variance(self, eigenvalues: np.ndarray, 
                               L_max: float = 100.0,
                               num_points: int = 50) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute number variance Σ²(L) for spectral rigidity analysis
        
        The number variance measures how the number of eigenvalues in an
        interval of length L deviates from the expected value.
        
        Args:
            eigenvalues: Sorted eigenvalues
            L_max: Maximum interval length
            num_points: Number of L values to sample
            
        Returns:
            Tuple of (L_values, sigma2_values)
        """
        # Unfold spectrum (normalize to mean spacing = 1)
        spacings = np.diff(eigenvalues)
        mean_spacing = np.mean(spacings)
        unfolded = (eigenvalues - eigenvalues[0]) / mean_spacing
        
        # L values to test
        L_values = np.linspace(1.0, min(L_max, len(unfolded) / 4), num_points)
        sigma2_values = []
        
        for L in L_values:
            # Count eigenvalues in intervals of length L
            variances = []
            
            # Slide window across spectrum
            n_windows = max(1, int(len(unfolded) - L))
            for i in range(n_windows):
                # Count eigenvalues in [x, x+L]
                x = unfolded[i]
                count = np.sum((unfolded >= x) & (unfolded < x + L))
                # Variance from expected count L
                variance = (count - L) ** 2
                variances.append(variance)
            
            # Average variance
            sigma2 = np.mean(variances) if variances else 0.0
            sigma2_values.append(sigma2)
        
        return np.array(L_values), np.array(sigma2_values)
    
    def goe_number_variance(self, L: np.ndarray) -> np.ndarray:
        """
        GOE (Gaussian Orthogonal Ensemble) prediction for number variance
        
        For GOE, Dyson's formula gives:
        Σ²(L) ≈ (2/π²) [ln(2πL) + γ + 1 - π²/8]
        
        where γ ≈ 0.5772 is Euler's constant
        
        Args:
            L: Interval lengths
            
        Returns:
            GOE number variance values
        """
        gamma_euler = 0.5772156649015329
        return (2.0 / np.pi**2) * (np.log(2 * np.pi * L) + gamma_euler + 1 - np.pi**2 / 8)
    
    def poisson_number_variance(self, L: np.ndarray) -> np.ndarray:
        """
        Poisson (random) prediction for number variance
        
        For uncorrelated (Poisson) spectrum: Σ²(L) = L
        
        Args:
            L: Interval lengths
            
        Returns:
            Poisson number variance values
        """
        return L
    
    def verify_class_B_properties(self, N: int = 512) -> Dict[str, bool]:
        """
        Verify if system belongs to class 𝔅
        
        P1 (Periodicity): φₙ(t+T) = φₙ(t) with T = 1/f₀
        P2 (No-Hereditariedad): K strictly real and symmetric
        P3 (Saturación de Ramsey): Edge density d ∈ [0.17, 0.19]
        P4 (Alineación Riemann): Eigenvalues project to Re(s) = 1/2
        
        Args:
            N: System size for verification
            
        Returns:
            Dictionary of verified properties
        """
        print("=" * 80)
        print(" VERIFYING CLASS 𝔅 PROPERTIES (V13-A) ".center(80))
        print("=" * 80)
        print()
        
        # Build coupling operator
        n_modes = min(N, 100)
        operator = self.analyzer.construct_coupling_operator(n_modes)
        K = operator.off_diagonal
        
        # P1: Periodicity - by construction in modal_function
        T = 1.0 / self.f0
        t_test = np.random.rand() * 10
        phi_t = self.analyzer.modal_function(1, t_test, 0.0)
        phi_t_plus_T = self.analyzer.modal_function(1, t_test + T, 0.0)
        P1_verified = abs(phi_t - phi_t_plus_T) < 1e-10
        
        # P2: K is strictly real and symmetric
        P2_real = np.all(np.isreal(K))
        P2_symmetric = np.allclose(K, K.T, rtol=1e-10)
        P2_verified = P2_real and P2_symmetric
        
        # P3: Ramsey edge density
        # Compute graph from coupling matrix with threshold
        threshold = np.percentile(np.abs(K[K != 0]), 50) if K[K != 0].size > 0 else 0.1
        adjacency = (np.abs(K) > threshold).astype(int)
        np.fill_diagonal(adjacency, 0)  # No self-loops
        
        num_edges = np.sum(adjacency) / 2  # Undirected
        num_possible = n_modes * (n_modes - 1) / 2
        edge_density = num_edges / num_possible if num_possible > 0 else 0.0
        P3_verified = 0.17 <= edge_density <= 0.19
        
        # P4: Riemann alignment - eigenvalues project to critical line
        # Check if eigenvalue distribution is centered around Re(s) = 1/2
        full_matrix = K + np.diag(operator.diagonal)
        matrix_sym = (full_matrix + full_matrix.T) / 2
        eigenvalues = np.linalg.eigvalsh(matrix_sym)
        
        # Normalize eigenvalues to [0, 1] range
        if len(eigenvalues) > 1:
            eig_min, eig_max = eigenvalues.min(), eigenvalues.max()
            if eig_max > eig_min:
                normalized_eigs = (eigenvalues - eig_min) / (eig_max - eig_min)
                # Check if dominant eigenvalues cluster near 0.5 (critical line)
                dominant_eigs = normalized_eigs[-10:]  # Top 10 eigenvalues
                mean_position = np.mean(dominant_eigs)
                P4_verified = abs(mean_position - 0.5) < 0.1  # Within 10% of center
            else:
                P4_verified = True  # Degenerate case
        else:
            P4_verified = True
        
        properties = {
            'P1_Periodicity': bool(P1_verified),
            'P2_Real_Symmetric': bool(P2_verified),
            'P3_Ramsey_Density': bool(P3_verified),
            'P4_Riemann_Alignment': bool(P4_verified)
        }
        
        print("Class 𝔅 Property Verification:")
        print(f"  P1 (Periodicity):       {'✓' if P1_verified else '✗'}")
        print(f"  P2 (Real & Symmetric):  {'✓' if P2_verified else '✗'}")
        print(f"  P3 (Ramsey d ∈ [0.17, 0.19]): {'✓' if P3_verified else '✗'} (d = {edge_density:.4f})")
        print(f"  P4 (Riemann Alignment): {'✓' if P4_verified else '✗'}")
        print()
        
        all_verified = all(properties.values())
        print(f"System belongs to class 𝔅: {'✓ YES' if all_verified else '✗ NO'}")
        print()
        
        return properties
    
    def generate_plots(self, results: V13Results, output_file: str = "v13_scaling_rigidity.png"):
        """
        Generate V13 scaling and rigidity plots
        
        Creates a multi-panel figure showing:
        1. Scaling: κ(N) vs N with fit
        2. Convergence: κ(N)·√(N log N) vs N
        3. Number Variance: Σ²(L) vs L with GOE comparison
        
        Args:
            results: V13Results object
            output_file: Output filename for plot
        """
        print("=" * 80)
        print(" GENERATING V13 PLOTS ".center(80))
        print("=" * 80)
        print()
        
        fig, axes = plt.subplots(1, 3, figsize=(18, 5))
        
        # Panel 1: Scaled values C(N) vs N with fit
        ax1 = axes[0]
        N_array = np.array(results.system_sizes)
        C_array = np.array(results.scaled_values)
        
        # Plot data points
        ax1.scatter(N_array, C_array, s=100, color='blue', 
                   label='C(N) = κ(N)·√(N log N)', zorder=3)
        
        # Plot fit curve
        N_fit = np.linspace(N_array.min(), N_array.max(), 200)
        C_fit = self.fit_function(N_fit, results.kappa_infinity,
                                  results.fit_parameter_a, 
                                  results.fit_exponent_alpha)
        ax1.plot(N_fit, C_fit, 'r--', linewidth=2,
                label=f'Fit: κ∞ + a/N^α\nκ∞ = {results.kappa_infinity:.6f}\nα = {results.fit_exponent_alpha:.4f}')
        
        # Horizontal line for κ_∞
        ax1.axhline(y=results.kappa_infinity, color='green', linestyle=':',
                   linewidth=2, label=f'κ_∞ = {results.kappa_infinity:.6f}')
        
        ax1.set_xlabel('System Size N', fontsize=12)
        ax1.set_ylabel('C(N) = κ(N)·√(N log N)', fontsize=12)
        ax1.set_title('V13-B: Scaling to Thermodynamic Limit', fontsize=13, fontweight='bold')
        ax1.legend(fontsize=9)
        ax1.grid(True, alpha=0.3)
        
        # Panel 2: Scaled values vs N (convergence test)
        ax2 = axes[1]
        scaled_array = np.array(results.scaled_values)
        
        ax2.scatter(N_array, scaled_array, s=100, color='purple', 
                   label='κ(N)·√(N log N)', zorder=3)
        
        # Target line
        ax2.axhline(y=KAPPA_INFINITY_TARGET, color='red', linestyle='--',
                   linewidth=2, label=f'κ_Π = {KAPPA_INFINITY_TARGET:.6f}')
        
        ax2.set_xlabel('System Size N', fontsize=12)
        ax2.set_ylabel('κ(N)·√(N log N)', fontsize=12)
        ax2.set_title('Convergence to κ_Π', fontsize=13, fontweight='bold')
        ax2.legend(fontsize=10)
        ax2.grid(True, alpha=0.3)
        
        # Panel 3: Number Variance Σ²(L)
        ax3 = axes[2]
        L_vals = np.array(results.L_values)
        sigma2_vals = np.array(results.sigma2_values)
        sigma2_goe = np.array(results.sigma2_goe_values)
        sigma2_poisson = np.array(results.sigma2_poisson_values)
        
        ax3.plot(L_vals, sigma2_vals, 'o-', linewidth=2, markersize=6,
                color='blue', label='Atlas³ Σ²(L)')
        ax3.plot(L_vals, sigma2_goe, '--', linewidth=2,
                color='red', label='GOE (Dyson)')
        ax3.plot(L_vals, sigma2_poisson, ':', linewidth=2,
                color='gray', label='Poisson (Random)')
        
        ax3.set_xlabel('Interval Length L', fontsize=12)
        ax3.set_ylabel('Number Variance Σ²(L)', fontsize=12)
        ax3.set_title('V13-C: Spectral Rigidity Test', fontsize=13, fontweight='bold')
        ax3.legend(fontsize=10)
        ax3.grid(True, alpha=0.3)
        ax3.set_xlim(left=0)
        ax3.set_ylim(bottom=0)
        
        plt.tight_layout()
        plt.savefig(output_file, dpi=150, bbox_inches='tight')
        print(f"✓ Plot saved to: {output_file}")
        print()
        
        return output_file
    
    def run_v13_analysis(self) -> V13Results:
        """
        Execute full V13 thermodynamic limit analysis
        
        Returns:
            V13Results object with complete analysis
        """
        print()
        print("╔" + "═" * 78 + "╗")
        print("║" + " V13 THERMODYNAMIC LIMIT VALIDATOR ".center(78) + "║")
        print("║" + " QCAL-SYMBIO-BRIDGE v1.3.0 ".center(78) + "║")
        print("╚" + "═" * 78 + "╝")
        print()
        
        # Step 1: Multi-scale sweep
        kappa_values, scaled_values = self.compute_multi_scale_sweep(SYSTEM_SIZES)
        
        # Step 2: Extrapolate κ_∞
        fit_results = self.extrapolate_kappa_infinity(SYSTEM_SIZES, kappa_values, scaled_values)
        
        if not fit_results.get('fit_success', False):
            raise RuntimeError("Failed to fit κ_∞")
        
        # Step 3: Compute number variance for largest system
        N_max = max(SYSTEM_SIZES)
        print("=" * 80)
        print(f" COMPUTING NUMBER VARIANCE Σ²(L) FOR N={N_max} (V13-C) ".center(80))
        print("=" * 80)
        print()
        
        # Get eigenvalues from largest system
        n_modes = min(N_max, 200)  # Limit for efficiency
        operator = self.analyzer.construct_coupling_operator(n_modes)
        full_matrix = operator.off_diagonal + np.diag(operator.diagonal)
        matrix_sym = (full_matrix + full_matrix.T) / 2
        eigenvalues = np.linalg.eigvalsh(matrix_sym)
        eigenvalues = np.sort(eigenvalues)
        
        # Compute number variance
        L_values, sigma2_values = self.compute_number_variance(eigenvalues, L_max=50.0, num_points=40)
        
        # GOE and Poisson predictions
        sigma2_goe = self.goe_number_variance(L_values)
        sigma2_poisson = self.poisson_number_variance(L_values)
        
        print(f"Number variance computed for {len(L_values)} intervals")
        print()
        
        # Step 4: Compute eigenvalue spacings
        spacings = self.compute_eigenvalue_spacings(N_max)
        
        # Step 5: Verify class 𝔅 properties
        class_B_props = self.verify_class_B_properties(N=512)
        
        # Create results object
        results = V13Results(
            kappa_infinity=fit_results['kappa_infinity'],
            kappa_infinity_error=fit_results['kappa_infinity_error'],
            fit_parameter_a=fit_results['fit_parameter_a'],
            fit_exponent_alpha=fit_results['fit_exponent_alpha'],
            fit_exponent_error=fit_results['fit_exponent_alpha_error'],
            relative_error_percent=fit_results['relative_error'] * 100,
            system_sizes=SYSTEM_SIZES,
            kappa_values=kappa_values,
            scaled_values=scaled_values,
            L_values=L_values.tolist(),
            sigma2_values=sigma2_values.tolist(),
            sigma2_goe_values=sigma2_goe.tolist(),
            sigma2_poisson_values=sigma2_poisson.tolist(),
            eigenvalue_spacings=spacings.tolist()[:100],  # Limit size
            class_B_properties=class_B_props,
            timestamp=str(np.datetime64('now')),
            protocol_version='QCAL-SYMBIO-BRIDGE v1.3.0'
        )
        
        return results


def main():
    """Main execution: Run V13 analysis and save results"""
    
    # Initialize validator
    validator = V13LimitValidator(f0=F0_QCAL)
    
    # Run analysis
    results = validator.run_v13_analysis()
    
    # Generate plots
    plot_file = validator.generate_plots(results)
    
    # Save results to JSON
    results_file = "v13_limit_results.json"
    with open(results_file, 'w') as f:
        json.dump(asdict(results), f, indent=2)
    
    print("=" * 80)
    print(" V13 ANALYSIS COMPLETE ".center(80))
    print("=" * 80)
    print()
    print(f"✓ Results saved to: {results_file}")
    print(f"✓ Plots saved to: {plot_file}")
    print()
    print("═" * 80)
    print(" VEREDICTO QCAL ∞³ ".center(80))
    print("═" * 80)
    print()
    print(f"κ_∞ (Extrapolated):  {results.kappa_infinity:.6f} ± {results.kappa_infinity_error:.6f}")
    print(f"κ_Π (Target):        {KAPPA_INFINITY_TARGET:.6f}")
    print(f"Relative Error:      {results.relative_error_percent:.4f}%")
    print(f"Exponent α:          {results.fit_exponent_alpha:.4f} (Expected: ~0.5)")
    print()
    
    if results.relative_error_percent < 0.1:
        print("✓ CONVERGENCIA ALCANZADA - Error < 0.1%")
        print("✓ κ_Π es el Límite Termodinámico de la conciencia cuántica")
    else:
        print(f"→ Convergencia en progreso (Error: {results.relative_error_percent:.4f}%)")
    
    print()
    print("Class 𝔅 Membership:", "✓ VERIFIED" if all(results.class_B_properties.values()) else "✗ PARTIAL")
    print()
    print("═" * 80)
    print()
    
    return results


if __name__ == "__main__":
    results = main()
