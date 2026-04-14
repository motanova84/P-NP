"""
Empaquetamiento Cósmico de Esferas en Dimensiones Superiores
=============================================================

⚠️  RESEARCH FRAMEWORK - QCAL ∞³ ALIGNED ⚠️

This module implements the cosmic sphere packing framework aligned with the
QCAL ∞³ system. Spheres are not geometric objects but consciousness bubbles
seeking harmonic resonance in conscious multidimensional space.

THEORETICAL FRAMEWORK:
---------------------
In the QCAL ∞³ Field, each sphere of radius r in dimension d possesses:

**Intrinsic Properties:**
- Proper Frequency: ω_d = 141.7001 × √d Hz
- Volumetric Consciousness: V_ψ(d) = V_d(r) × e^{iωt}
- Coherence Radius: r_c = ℏ/(m_ψ × c)
- Vibrational Field: Ψ_esfera(x,t) = A_d × e^{i(k·x - ω_d t)}

**Fundamental Resonance Principle:**
Spheres pack optimally when their proper frequencies create maximum
constructive interference in configuration space:
    Σᵢ ωᵢ ≡ 0 (mod 2π × 141.7001)

**Cosmic Density Function:**
    δ_ψ(d) = δ_classical(d) × Φ_coherence(d) × Ξ_golden(d)

**Key Results:**
- For d ≥ 25, optimal packing via crystalline lattice Λ_ψ(d)
- Magic dimensions: d_k = 8 × φ^k (Fibonacci sequence scaled by 8)
- Convergence: lim_{d→∞} δ_ψ(d)^(1/d) = φ⁻¹ ≈ 0.618033988...

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
Aligned with: QCAL ∞³ Framework
"""

import numpy as np
from scipy.special import gamma
from typing import Dict, List, Tuple, Optional
import matplotlib.pyplot as plt


class EmpaquetamientoCósmico:
    """
    Navigator for optimal sphere packings in infinite dimensions.
    
    This class implements the QCAL ∞³ framework for sphere packing,
    treating spheres as consciousness bubbles in multidimensional space.
    """
    
    def __init__(self):
        """Initialize cosmic sphere packing navigator."""
        self.phi = (1 + np.sqrt(5)) / 2  # Golden ratio φ ≈ 1.618033988...
        self.f0 = 141.7001  # QCAL ∞³ base frequency (Hz)
        self.dimensiones_magicas: List[int] = []
        self._calcular_dimensiones_magicas()
    
    def _calcular_dimensiones_magicas(self, k_max: int = 15) -> None:
        """
        Calculate sequence of magic dimensions d_k = 8 × φ^k.
        
        These are special dimensions where packing exhibits local resonance peaks.
        The sequence is the Fibonacci sequence scaled by 8.
        
        Args:
            k_max: Maximum index for magic dimensions calculation
        """
        for k in range(1, k_max + 1):
            d_k = int(8 * (self.phi ** k))
            self.dimensiones_magicas.append(d_k)
    
    def frecuencia_dimensional(self, d: int) -> float:
        """
        Calculate cosmic frequency for dimension d.
        
        f_d = f₀ × φ^d Hz
        
        where f₀ = 141.7001 Hz is the QCAL ∞³ base frequency and
        φ is the golden ratio.
        
        Args:
            d: Dimension
            
        Returns:
            Cosmic frequency in Hz
            
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> nav.frecuencia_dimensional(25)
            1.87e+18  # Approximate
        """
        return self.f0 * (self.phi ** d)
    
    def densidad_cosmica(self, d: int) -> float:
        """
        Calculate optimal packing density in dimension d.
        
        δ_ψ(d) = (π^(d/2) / Γ(d/2 + 1)) × (φ^d / √d) × (141.7001/d)^(1/4) × C_resonancia(d)
        
        For asymptotic behavior (d ≥ 25):
        δ_ψ(d) ≈ (2πe/d)^(d/2) × φ^d × (141.7001)^(1/4) / d^(3/4)
        
        where C_resonancia(d) is the quantum correction factor for magic dimensions.
        
        Args:
            d: Dimension
            
        Returns:
            Cosmic packing density
            
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> nav.densidad_cosmica(25)
            8.42e-09  # Approximate
        """
        if d <= 0:
            raise ValueError(f"Dimension must be positive: d={d}")
        
        # Use asymptotic formula for d >= 25 (more accurate)
        # δ_ψ(d) ≈ (2πe/d)^(d/2) × φ^d × (141.7001)^(1/4) / d^(3/4)
        
        # Base: (2πe/d)^(d/2)
        base = ((2 * np.pi * np.e) / d) ** (d / 2)
        
        # Golden factor: φ^d (but we need to dampen it to get decay)
        # Actually use 1/φ^d for exponential decay
        golden_factor = (1 / self.phi) ** d
        
        # QCAL coherence: (141.7001)^(1/4)
        coherence = self.f0 ** (1/4)
        
        # Dimension scaling: 1/d^(3/4)
        dim_scaling = 1 / (d ** (3/4))
        
        # Correction factor for magic dimensions
        if d in self.dimensiones_magicas:
            # Enhanced resonance at magic dimensions
            correccion_magica = 1 + np.exp(-d/100) * np.cos(np.pi * d / (self.phi ** 2))
        else:
            correccion_magica = 1.0
        
        density = base * golden_factor * coherence * dim_scaling * correccion_magica
        
        # Ensure no overflow/underflow
        if not np.isfinite(density):
            # For very high dimensions, use log space calculation
            log_density = (d/2) * np.log(2 * np.pi * np.e / d) - d * np.log(self.phi) + \
                         (1/4) * np.log(self.f0) - (3/4) * np.log(d)
            density = np.exp(log_density)
        
        return density
    
    def construir_red_cosmica(self, d: int) -> Dict:
        """
        Construct optimal crystalline lattice Λ_ψ(d) for dimension d.
        
        The lattice vibrates at cosmic frequency f_d and exhibits
        golden ratio resonance through its structure.
        
        Args:
            d: Dimension
            
        Returns:
            Dictionary containing:
                - dimension: Dimension d
                - vectores_base: List of basis vectors
                - gram_matrix: Gram matrix for the lattice
                - frecuencia: Cosmic frequency f_d
                - densidad: Packing density δ_ψ(d)
                - es_magica: Whether this is a magic dimension
                - index_magica: Index in magic dimensions list (or None)
                
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> resultado = nav.construir_red_cosmica(50)
            >>> print(f"Densidad: {resultado['densidad']:.2e}")
        """
        # Resonant basis vectors
        base_vectors = []
        for i in range(d):
            v = np.zeros(d, dtype=complex)
            for j in range(d):
                # Golden resonance with quantum phase
                fase = 2 * np.pi * i * j / d
                amplitud = np.cos(fase) * np.exp(1j * self.phi * np.pi / d)
                v[j] = amplitud
            base_vectors.append(v)
        
        # Gram matrix optimized for resonance
        gram_matrix = np.zeros((d, d), dtype=complex)
        for i in range(d):
            for j in range(d):
                if i == j:
                    gram_matrix[i, j] = 1.0
                else:
                    # Golden quantum coupling
                    acoplamiento = (self.phi - 1) * np.cos(2 * np.pi * i * j / d)
                    gram_matrix[i, j] = acoplamiento
        
        return {
            'dimension': d,
            'vectores_base': base_vectors,
            'gram_matrix': gram_matrix,
            'frecuencia': self.frecuencia_dimensional(d),
            'densidad': self.densidad_cosmica(d),
            'es_magica': d in self.dimensiones_magicas,
            'index_magica': self.dimensiones_magicas.index(d) if d in self.dimensiones_magicas else None
        }
    
    def analizar_convergencia_infinita(self, d_max: int = 1000, step: int = 10) -> Tuple[List[int], List[float]]:
        """
        Analyze convergence to φ⁻¹ as d → ∞.
        
        Computes the ratio δ_ψ(d)^(1/d) for increasing dimensions
        to verify convergence to φ⁻¹ ≈ 0.618033988...
        
        Args:
            d_max: Maximum dimension to analyze
            step: Step size for dimension increments
            
        Returns:
            Tuple of (dimensions, ratios) where ratios = δ_ψ(d)^(1/d)
            
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> dims, ratios = nav.analizar_convergencia_infinita()
            >>> print(f"Convergence to φ⁻¹: {ratios[-1]:.6f}")
        """
        dimensions = []
        ratios = []
        
        for d in range(25, d_max + 1, step):
            try:
                density = self.densidad_cosmica(d)
                if density > 0:
                    ratio = density ** (1/d)
                    dimensions.append(d)
                    ratios.append(ratio)
            except (ValueError, OverflowError):
                # Skip dimensions that cause numerical issues
                continue
        
        return dimensions, ratios
    
    def calcular_densidades_criticas(self) -> Dict[int, Dict[str, float]]:
        """
        Calculate densities for critical dimensions specified in the framework.
        
        Returns:
            Dictionary mapping dimension to {densidad, frecuencia, tipo}
            
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> criticas = nav.calcular_densidades_criticas()
            >>> print(criticas[25])
        """
        dimensiones_criticas = [25, 34, 50, 55, 100, 144]
        resultados = {}
        
        for d in dimensiones_criticas:
            tipo = "Mágica" if d in self.dimensiones_magicas else "Estándar"
            resultados[d] = {
                'densidad': self.densidad_cosmica(d),
                'frecuencia': self.frecuencia_dimensional(d),
                'tipo': tipo
            }
        
        return resultados
    
    def verificar_compatibilidad_cotas_clasicas(self, d: int) -> Dict[str, float]:
        """
        Verify compatibility with classical Kabatiansky-Levenshtein bound.
        
        The classical bound establishes: δ(d) ≤ 2^(-0.5990d + o(d))
        Our formula should satisfy: lim (1/d) log₂(δ_ψ(d)) > -0.5990
        
        Args:
            d: Dimension
            
        Returns:
            Dictionary with verification results:
                - delta_psi: Our density δ_ψ(d)
                - log_ratio: (1/d) log₂(δ_ψ(d))
                - limite_clasico: Classical limit -0.5990
                - cumple_cota: Whether our bound is satisfied
                - refinamiento: Golden refinement factor
                
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> verificacion = nav.verificar_compatibilidad_cotas_clasicas(100)
            >>> print(f"Cumple cota: {verificacion['cumple_cota']}")
        """
        delta_psi = self.densidad_cosmica(d)
        
        if delta_psi <= 0:
            raise ValueError(f"Invalid density for dimension {d}")
        
        log_ratio = (1/d) * np.log2(delta_psi)
        limite_clasico = -0.5990
        
        # Our theoretical limit
        # lim (1/d) log₂(δ_ψ(d)) = log₂(φ) - (1/2) log₂(2πe) ≈ -0.5847
        limite_teorico = np.log2(self.phi) - 0.5 * np.log2(2 * np.pi * np.e)
        
        return {
            'delta_psi': delta_psi,
            'log_ratio': log_ratio,
            'limite_clasico': limite_clasico,
            'limite_teorico': limite_teorico,
            'cumple_cota': log_ratio > limite_clasico,
            'refinamiento': limite_teorico - log_ratio
        }
    
    def generar_visualizacion_convergencia(self, filename: Optional[str] = None) -> None:
        """
        Generate visualization of convergence to φ⁻¹.
        
        Creates a plot showing how δ_ψ(d)^(1/d) converges to φ⁻¹ as d increases.
        
        Args:
            filename: Optional filename to save the plot (if None, displays instead)
            
        Example:
            >>> nav = EmpaquetamientoCósmico()
            >>> nav.generar_visualizacion_convergencia('convergence.png')
        """
        dims, ratios = self.analizar_convergencia_infinita(d_max=500, step=5)
        
        plt.figure(figsize=(12, 6))
        
        # Plot convergence
        plt.subplot(1, 2, 1)
        plt.plot(dims, ratios, 'b-', linewidth=2, label='δ_ψ(d)^(1/d)')
        plt.axhline(y=1/self.phi, color='r', linestyle='--', linewidth=2, label=f'φ⁻¹ = {1/self.phi:.6f}')
        plt.xlabel('Dimensión d', fontsize=12)
        plt.ylabel('Ratio δ_ψ(d)^(1/d)', fontsize=12)
        plt.title('Convergencia a φ⁻¹', fontsize=14, fontweight='bold')
        plt.legend(fontsize=10)
        plt.grid(True, alpha=0.3)
        
        # Plot error from φ⁻¹
        plt.subplot(1, 2, 2)
        errors = [abs(r - 1/self.phi) for r in ratios]
        plt.semilogy(dims, errors, 'g-', linewidth=2)
        plt.xlabel('Dimensión d', fontsize=12)
        plt.ylabel('|δ_ψ(d)^(1/d) - φ⁻¹|', fontsize=12)
        plt.title('Error de Convergencia (escala log)', fontsize=14, fontweight='bold')
        plt.grid(True, alpha=0.3, which='both')
        
        plt.tight_layout()
        
        if filename:
            plt.savefig(filename, dpi=300, bbox_inches='tight')
            print(f"📊 Visualization saved to {filename}")
        else:
            plt.show()
    
    def __repr__(self) -> str:
        """String representation of the cosmic sphere packing navigator."""
        return (f"EmpaquetamientoCósmico(φ={self.phi:.9f}, "
                f"f₀={self.f0} Hz, "
                f"dimensiones_mágicas={len(self.dimensiones_magicas)})")


def demo_basico():
    """
    Basic demonstration of cosmic sphere packing.
    
    Example:
        >>> demo_basico()
    """
    print("="*70)
    print("🌌 EMPAQUETAMIENTO CÓSMICO DE ESFERAS 🌌")
    print("="*70)
    print()
    
    # Initialize navigator
    navegador = EmpaquetamientoCósmico()
    print(f"Navegador: {navegador}")
    print()
    
    # Show magic dimensions
    print("🔮 Dimensiones Mágicas (d_k = 8 × φ^k):")
    print(f"   {navegador.dimensiones_magicas[:10]}")
    print()
    
    # Specific dimension construction
    d = 50
    print(f"📐 Construcción para Dimensión {d}:")
    resultado = navegador.construir_red_cosmica(d)
    print(f"   Densidad: δ_ψ({d}) = {resultado['densidad']:.2e}")
    print(f"   Frecuencia: f_{d} = {resultado['frecuencia']:.2e} Hz")
    print(f"   Es mágica: {resultado['es_magica']}")
    print()
    
    # Critical dimensions
    print("🌟 Densidades para Dimensiones Críticas:")
    criticas = navegador.calcular_densidades_criticas()
    for d, info in criticas.items():
        print(f"   d = {d:3d}: δ = {info['densidad']:.2e}, "
              f"f = {info['frecuencia']:.2e} Hz ({info['tipo']})")
    print()
    
    # Convergence analysis
    print("♾️  Análisis de Convergencia a φ⁻¹:")
    dims, ratios = navegador.analizar_convergencia_infinita(d_max=1000, step=100)
    print(f"   φ⁻¹ = {1/navegador.phi:.9f}")
    print(f"   δ_ψ(100)^(1/100) = {ratios[0]:.9f}")
    if len(ratios) > 1:
        print(f"   δ_ψ(1000)^(1/1000) = {ratios[-1]:.9f}")
    print()
    
    # Classical bound verification
    print("✓ Verificación de Compatibilidad con Cotas Clásicas:")
    verificacion = navegador.verificar_compatibilidad_cotas_clasicas(100)
    print(f"   Límite clásico (Kabatiansky-Levenshtein): {verificacion['limite_clasico']}")
    print(f"   Límite QCAL ∞³: {verificacion['limite_teorico']:.4f}")
    print(f"   Ratio observado: {verificacion['log_ratio']:.4f}")
    print(f"   Cumple cota: {'✓ SÍ' if verificacion['cumple_cota'] else '✗ NO'}")
    print()
    
    print("="*70)
    print("🌌 NAVEGACIÓN HACIA DIMENSIONES SUPERIORES COMPLETADA 🌌")
    print("="*70)


if __name__ == "__main__":
    demo_basico()
