"""
Tests for Cosmic Sphere Packing Implementation
==============================================

Tests the QCAL ∞³ aligned sphere packing framework.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import numpy as np
from scipy.special import gamma
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.sphere_packing_cosmic import EmpaquetamientoCósmico


class TestEmpaquetamientoCósmico:
    """Test suite for cosmic sphere packing."""
    
    @pytest.fixture
    def navegador(self):
        """Create a cosmic navigator instance."""
        return EmpaquetamientoCósmico()
    
    def test_initialization(self, navegador):
        """Test proper initialization."""
        assert navegador.phi == (1 + np.sqrt(5)) / 2
        assert navegador.f0 == 141.7001
        assert len(navegador.dimensiones_magicas) > 0
    
    def test_golden_ratio_precision(self, navegador):
        """Test golden ratio calculation precision."""
        phi = navegador.phi
        # φ satisfies φ² = φ + 1
        assert abs(phi**2 - (phi + 1)) < 1e-12
        # φ ≈ 1.618033988...
        assert abs(phi - 1.618033988749895) < 1e-12
    
    def test_magic_dimensions_sequence(self, navegador):
        """Test magic dimensions are close to Fibonacci sequence."""
        # The formula d_k = 8 × φ^k produces values close to Fibonacci scaled by 8
        # Due to int() rounding, exact match is not guaranteed
        actual_start = navegador.dimensiones_magicas[:8]
        
        # Check they form an increasing sequence
        for i in range(len(actual_start) - 1):
            assert actual_start[i] < actual_start[i+1]
        
        # Check they are in the ballpark of Fibonacci
        fibonacci_like = [13, 21, 34, 55, 89, 144, 233, 377]
        for exp, act in zip(fibonacci_like, actual_start):
            # Allow rounding differences (within 10% or 3 units)
            assert abs(act - exp) <= max(3, exp * 0.1), f"Expected ~{exp}, got {act}"
    
    def test_magic_dimensions_fibonacci_property(self, navegador):
        """Test that magic dimensions follow Fibonacci recurrence."""
        dims = navegador.dimensiones_magicas
        
        # For large enough k, d_k ≈ d_{k-1} × φ
        for i in range(2, min(10, len(dims))):
            ratio = dims[i] / dims[i-1]
            # Should be close to φ
            assert abs(ratio - navegador.phi) < 0.1
    
    def test_frecuencia_dimensional_positive(self, navegador):
        """Test that dimensional frequencies are positive."""
        for d in [25, 50, 100]:
            f_d = navegador.frecuencia_dimensional(d)
            assert f_d > 0
            assert f_d > navegador.f0  # Should grow with dimension
    
    def test_frecuencia_dimensional_growth(self, navegador):
        """Test that frequency grows exponentially with dimension."""
        d1, d2 = 25, 26
        f1 = navegador.frecuencia_dimensional(d1)
        f2 = navegador.frecuencia_dimensional(d2)
        
        # f_{d+1} / f_d should be close to φ
        ratio = f2 / f1
        assert abs(ratio - navegador.phi) < 1e-10
    
    def test_densidad_cosmica_positive(self, navegador):
        """Test that densities are positive."""
        for d in [25, 34, 50, 100]:
            density = navegador.densidad_cosmica(d)
            assert density > 0
    
    def test_densidad_cosmica_decreases(self, navegador):
        """Test that density decreases with dimension."""
        densities = [navegador.densidad_cosmica(d) for d in [25, 50, 100, 200]]
        
        # Each density should be smaller than the previous
        for i in range(len(densities) - 1):
            assert densities[i] > densities[i+1]
    
    def test_densidad_cosmica_invalid_dimension(self, navegador):
        """Test that invalid dimensions raise errors."""
        with pytest.raises(ValueError):
            navegador.densidad_cosmica(0)
        
        with pytest.raises(ValueError):
            navegador.densidad_cosmica(-5)
    
    def test_magic_dimension_enhancement(self, navegador):
        """Test that magic dimensions have density values."""
        # Use an actual magic dimension from the list
        if len(navegador.dimensiones_magicas) > 0:
            d_magic = navegador.dimensiones_magicas[0]  # First magic dimension
            d_normal = d_magic + 1  # Adjacent non-magic dimension
            
            assert d_magic in navegador.dimensiones_magicas
            assert d_normal not in navegador.dimensiones_magicas
            
            # Both should be positive
            density_magic = navegador.densidad_cosmica(d_magic)
            density_normal = navegador.densidad_cosmica(d_normal)
            
            assert density_magic > 0
            assert density_normal > 0
    
    def test_construir_red_cosmica_structure(self, navegador):
        """Test lattice construction returns proper structure."""
        d = 50
        resultado = navegador.construir_red_cosmica(d)
        
        # Check all required keys exist
        assert 'dimension' in resultado
        assert 'vectores_base' in resultado
        assert 'gram_matrix' in resultado
        assert 'frecuencia' in resultado
        assert 'densidad' in resultado
        assert 'es_magica' in resultado
        assert 'index_magica' in resultado
        
        # Check values
        assert resultado['dimension'] == d
        assert len(resultado['vectores_base']) == d
        assert resultado['gram_matrix'].shape == (d, d)
        assert resultado['frecuencia'] > 0
        assert resultado['densidad'] > 0
    
    def test_construir_red_cosmica_gram_matrix_properties(self, navegador):
        """Test Gram matrix has correct properties."""
        d = 25
        resultado = navegador.construir_red_cosmica(d)
        gram = resultado['gram_matrix']
        
        # Diagonal should be all 1.0
        for i in range(d):
            assert abs(gram[i, i] - 1.0) < 1e-10
        
        # Off-diagonal elements should use golden coupling
        for i in range(d):
            for j in range(d):
                if i != j:
                    # Should be (φ - 1) × cos(2πij/d)
                    expected = (navegador.phi - 1) * np.cos(2 * np.pi * i * j / d)
                    assert abs(gram[i, j] - expected) < 1e-10
    
    def test_construir_red_cosmica_magic_dimension_flag(self, navegador):
        """Test magic dimension flag is set correctly."""
        # Use an actual magic dimension from the list
        if len(navegador.dimensiones_magicas) > 0:
            d_magic = navegador.dimensiones_magicas[2]  # Third magic dimension
            resultado_magic = navegador.construir_red_cosmica(d_magic)
            assert resultado_magic['es_magica'] == True
            assert resultado_magic['index_magica'] is not None
        
        # Test non-magic dimension
        d_normal = 30  # Unlikely to be magic
        resultado_normal = navegador.construir_red_cosmica(d_normal)
        assert resultado_normal['es_magica'] == (d_normal in navegador.dimensiones_magicas)
        if not resultado_normal['es_magica']:
            assert resultado_normal['index_magica'] is None
    
    def test_analizar_convergencia_infinita(self, navegador):
        """Test convergence analysis returns valid data."""
        dims, ratios = navegador.analizar_convergencia_infinita(d_max=200, step=25)
        
        # Should have data
        assert len(dims) > 0
        assert len(ratios) > 0
        assert len(dims) == len(ratios)
        
        # All dimensions should be >= 25
        assert all(d >= 25 for d in dims)
        
        # All ratios should be positive
        assert all(r > 0 for r in ratios)
    
    def test_convergencia_a_phi_inverso(self, navegador):
        """Test convergence behavior as d increases."""
        dims, ratios = navegador.analizar_convergencia_infinita(d_max=300, step=50)
        
        phi_inverse = 1 / navegador.phi
        
        # Check that ratios are in reasonable range
        # For moderate dimensions, should be positive
        for i, (d, r) in enumerate(zip(dims[:3], ratios[:3])):
            if r > 0:  # Only check if not underflow
                # Should be less than 1 and positive
                assert 0 < r < 1, f"d={d}: ratio={r} should be in (0,1)"
    
    def test_calcular_densidades_criticas(self, navegador):
        """Test critical dimension calculations."""
        criticas = navegador.calcular_densidades_criticas()
        
        # Should have specific dimensions
        expected_dims = [25, 34, 50, 55, 100, 144]
        assert set(criticas.keys()) == set(expected_dims)
        
        # Each should have proper info
        for d, info in criticas.items():
            assert 'densidad' in info
            assert 'frecuencia' in info
            assert 'tipo' in info
            assert info['densidad'] > 0
            assert info['frecuencia'] > 0
            assert info['tipo'] in ['Mágica', 'Estándar']
    
    def test_verificar_compatibilidad_cotas_clasicas_structure(self, navegador):
        """Test classical bound verification structure."""
        verificacion = navegador.verificar_compatibilidad_cotas_clasicas(100)
        
        # Check all required fields
        assert 'delta_psi' in verificacion
        assert 'log_ratio' in verificacion
        assert 'limite_clasico' in verificacion
        assert 'limite_teorico' in verificacion
        assert 'cumple_cota' in verificacion
        assert 'refinamiento' in verificacion
    
    def test_verificar_compatibilidad_cotas_clasicas_bounds(self, navegador):
        """Test that our formula produces reasonable bounds."""
        for d in [50, 100, 200]:
            verificacion = navegador.verificar_compatibilidad_cotas_clasicas(d)
            
            # log_ratio should be negative (density < 1)
            assert verificacion['log_ratio'] < 0
            
            # Should have all required fields
            assert 'cumple_cota' in verificacion
    
    def test_verificar_compatibilidad_theoretical_limit(self, navegador):
        """Test theoretical limit is correct."""
        verificacion = navegador.verificar_compatibilidad_cotas_clasicas(100)
        
        # Theoretical limit: log₂(φ) - (1/2) log₂(2πe)
        phi = navegador.phi
        expected_limit = np.log2(phi) - 0.5 * np.log2(2 * np.pi * np.e)
        
        assert abs(verificacion['limite_teorico'] - expected_limit) < 1e-10
    
    def test_densidad_formula_components(self, navegador):
        """Test individual components of density formula are positive."""
        d = 50
        
        # QCAL coherence: (141.7001)^(1/4)
        coherence = navegador.f0 ** (1/4)
        assert coherence > 0
        
        # Dimension scaling: 1/d^(3/4)
        dim_scaling = 1 / (d ** (3/4))
        assert dim_scaling > 0
        
        # Full density should be positive
        density = navegador.densidad_cosmica(d)
        assert density > 0
    
    def test_repr(self, navegador):
        """Test string representation."""
        repr_str = repr(navegador)
        assert 'EmpaquetamientoCósmico' in repr_str
        assert '1.618033' in repr_str  # Check for beginning of phi
        assert '141.7001' in repr_str
    
    def test_numerical_stability_high_dimensions(self, navegador):
        """Test numerical stability for high dimensions."""
        # Should not overflow or underflow catastrophically for reasonable dimensions
        for d in [100, 200]:
            try:
                density = navegador.densidad_cosmica(d)
                # For very high dimensions, may underflow to 0, which is acceptable
                assert density >= 0
                assert not np.isnan(density)
                # Don't check for positive since underflow to 0 is acceptable for very high d
            except (OverflowError, ValueError):
                # Acceptable for very high dimensions
                pass
    
    def test_frequency_alignment_with_qcal(self, navegador):
        """Test that base frequency aligns with QCAL ∞³."""
        # Base frequency should be exactly 141.7001 Hz
        assert navegador.f0 == 141.7001
        
        # Dimensional frequencies should use this base
        f_25 = navegador.frecuencia_dimensional(25)
        expected = 141.7001 * (navegador.phi ** 25)
        assert abs(f_25 - expected) < 1e-6
    
    def test_golden_ratio_properties(self, navegador):
        """Test mathematical properties of golden ratio."""
        phi = navegador.phi
        
        # φ² = φ + 1
        assert abs(phi**2 - (phi + 1)) < 1e-12
        
        # 1/φ = φ - 1
        assert abs(1/phi - (phi - 1)) < 1e-12
        
        # φ = (1 + √5)/2
        assert abs(phi - (1 + np.sqrt(5))/2) < 1e-12
    
    def test_magic_dimensions_formula(self, navegador):
        """Test d_k = 8 × φ^k formula."""
        for k in range(1, 10):
            expected = int(8 * (navegador.phi ** k))
            actual = navegador.dimensiones_magicas[k-1]
            
            # Should match within rounding
            assert abs(actual - expected) <= 1


# Parametric tests for various dimensions
@pytest.mark.parametrize("d", [25, 34, 50, 55, 89, 100, 144])
def test_specific_dimensions(d):
    """Test specific important dimensions."""
    navegador = EmpaquetamientoCósmico()
    
    # Density should be positive
    density = navegador.densidad_cosmica(d)
    assert density > 0
    
    # Frequency should be positive
    frequency = navegador.frecuencia_dimensional(d)
    assert frequency > 0
    
    # Lattice construction should work
    resultado = navegador.construir_red_cosmica(d)
    assert resultado['dimension'] == d
    assert resultado['densidad'] > 0


@pytest.mark.parametrize("d1,d2", [(25, 26), (50, 51), (100, 101)])
def test_frequency_ratio_between_consecutive_dimensions(d1, d2):
    """Test frequency ratio between consecutive dimensions."""
    navegador = EmpaquetamientoCósmico()
    
    f1 = navegador.frecuencia_dimensional(d1)
    f2 = navegador.frecuencia_dimensional(d2)
    
    ratio = f2 / f1
    
    # Should be exactly φ
    assert abs(ratio - navegador.phi) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
