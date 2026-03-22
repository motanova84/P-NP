#!/usr/bin/env python3
"""
Test Suite for BSD Adélico Connector
====================================

Tests for BSD-ADN synchronization and Pentagon Logos closure.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ
"""

import sys
import os

# Add qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from qcal.adn_riemann import CodificadorADNRiemann
from qcal.bsd_adelic_connector import (
    sincronizar_bsd_adn,
    validar_pentagono_cerrado,
    calcular_capacidad_resonancia,
    analizar_familia_curvas,
    F0,
    NODOS_CONSTELACION
)


class TestCodificadorADNRiemann:
    """Test suite for ADN-Riemann encoder."""
    
    def test_initialization(self):
        """Test that CodificadorADNRiemann initializes correctly."""
        codif = CodificadorADNRiemann()
        
        assert codif.f0 == F0
        assert 'G' in codif.base_freqs
        assert codif.base_freqs['G'] == F0  # Guanina resuena con f0
    
    def test_secuencia_a_espectro(self):
        """Test DNA sequence to spectrum conversion."""
        codif = CodificadorADNRiemann()
        
        # Test simple sequence
        espectro = codif.secuencia_a_espectro("GACT")
        assert len(espectro) == 4
        assert espectro[0] == codif.base_freqs['G']
        assert espectro[1] == codif.base_freqs['A']
    
    def test_calcular_resonancia(self):
        """Test resonance calculation."""
        codif = CodificadorADNRiemann()
        
        # GGGG should have perfect resonance
        res_perfect = codif.calcular_resonancia("GGGG")
        assert abs(res_perfect - 1.0) < 0.001
        
        # GACT should have intermediate resonance
        res_mixed = codif.calcular_resonancia("GACT")
        assert 0.8 < res_mixed < 1.0
        
        # Empty sequence
        res_empty = codif.calcular_resonancia("")
        assert res_empty == 0.0
    
    def test_identificar_hotspots(self):
        """Test hotspot identification."""
        codif = CodificadorADNRiemann()
        
        # GACT: only G is a hotspot (resonance 1.0)
        hotspots = codif.identificar_hotspots("GACT")
        assert len(hotspots) == 1
        assert hotspots[0][0] == 0  # Position 0
        assert hotspots[0][1] == 'G'  # Base G
        assert hotspots[0][2] == 1.0  # Perfect resonance
        
        # GGGG: all are hotspots
        hotspots_all = codif.identificar_hotspots("GGGG")
        assert len(hotspots_all) == 4
    
    def test_hotspots_simple(self):
        """Test simplified hotspots function."""
        codif = CodificadorADNRiemann()
        
        hotspots = codif.hotspots("GACT")
        assert hotspots == [0]  # Only index 0 (G)
        
        hotspots_multi = codif.hotspots("GCGC")
        assert len(hotspots_multi) == 2  # G at positions 0 and 2
    
    def test_analizar_secuencia(self):
        """Test complete sequence analysis."""
        codif = CodificadorADNRiemann()
        
        analisis = codif.analizar_secuencia("GACT")
        
        assert analisis['longitud'] == 4
        assert 'resonancia_global' in analisis
        assert 'hotspots' in analisis
        assert 'num_hotspots' in analisis
        assert analisis['bases_g'] == 1
        assert analisis['bases_c'] == 1
        assert abs(analisis['proporcion_gc'] - 0.5) < 0.001  # 2/4 = 0.5


class TestBSDConnector:
    """Test suite for BSD Adelic Connector."""
    
    def test_sincronizar_bsd_adn_basic(self):
        """Test basic BSD-ADN synchronization."""
        # Curva de Mordell: y^2 = x^3 - x, rango r=1
        curva = {
            'rango_adelico': 1,
            'L_E1': 0.0
        }
        
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['rango_bio_aritmetico'] == 1
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['psi_bsd_qcal'] == 1.0
        assert resultado['hotspots_adn'] == 1
    
    def test_sincronizar_bsd_adn_superfluid(self):
        """Test superfluid condition when L(E,1)=0."""
        curva = {
            'rango_adelico': 2,
            'L_E1': 0.0  # BSD predicts L(E,1)=0 for r>0
        }
        
        resultado = sincronizar_bsd_adn(curva, "GCGC")
        
        # Should be superfluid (no viscosity)
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['psi_bsd_qcal'] == 1.0
        assert resultado['viscosidad_l_e1'] == 0.0
    
    def test_sincronizar_bsd_adn_dissipative(self):
        """Test dissipative flow when L(E,1) != 0."""
        curva = {
            'rango_adelico': 0,
            'L_E1': 0.5  # Non-zero viscosity
        }
        
        resultado = sincronizar_bsd_adn(curva, "ATCG")
        
        # Should be dissipative (with viscosity)
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
        assert resultado['psi_bsd_qcal'] == 0.5  # 1 - 0.5
        assert resultado['viscosidad_l_e1'] == 0.5
    
    def test_nodos_constelacion(self):
        """Test constellation node activation."""
        curva_r1 = {'rango_adelico': 1, 'L_E1': 0.0}
        res1 = sincronizar_bsd_adn(curva_r1, "G")
        assert res1['nodos_constelacion'] == 1
        
        curva_r2 = {'rango_adelico': 2, 'L_E1': 0.0}
        res2 = sincronizar_bsd_adn(curva_r2, "GG")
        assert res2['nodos_constelacion'] == 2
        
        # Should not exceed maximum
        curva_large = {'rango_adelico': 100, 'L_E1': 0.0}
        res_large = sincronizar_bsd_adn(curva_large, "GGGG")
        assert res_large['nodos_constelacion'] <= NODOS_CONSTELACION


class TestPentagonoValidacion:
    """Test suite for Pentagon Logos validation."""
    
    def test_validar_pentagono_cerrado_success(self):
        """Test successful Pentagon closure."""
        # Create a valid BSD result
        resultado_bsd = {
            'rango_bio_aritmetico': 1,
            'fluidez_info_ns': "INFINITA",
            'psi_bsd_qcal': 1.0,
            'hotspots_adn': 1
        }
        
        validacion = validar_pentagono_cerrado(resultado_bsd)
        
        assert validacion['pentagono_cerrado'] is True
        assert validacion['flujo_superfluido'] is True
        assert validacion['coherencia_maxima'] is True
        assert validacion['hotspots_activos'] is True
        assert validacion['milenio_unificados'] == 5
        assert len(validacion['problemas']) == 5
    
    def test_validar_pentagono_cerrado_failure(self):
        """Test Pentagon closure failure."""
        # Not superfluid
        resultado_bad = {
            'rango_bio_aritmetico': 0,
            'fluidez_info_ns': "DISIPATIVA",
            'psi_bsd_qcal': 0.5,
            'hotspots_adn': 0
        }
        
        validacion = validar_pentagono_cerrado(resultado_bad)
        
        assert validacion['pentagono_cerrado'] is False
        assert validacion['flujo_superfluido'] is False
        assert validacion['coherencia_maxima'] is False
        assert validacion['hotspots_activos'] is False
        assert validacion['milenio_unificados'] == 0


class TestUtilityFunctions:
    """Test suite for utility functions."""
    
    def test_calcular_capacidad_resonancia(self):
        """Test resonance capacity calculation."""
        cap_mutacion = calcular_capacidad_resonancia(1)
        assert cap_mutacion == "MUTACION_SALUD"
        
        cap_mutacion2 = calcular_capacidad_resonancia(5)
        assert cap_mutacion2 == "MUTACION_SALUD"
        
        cap_reposo = calcular_capacidad_resonancia(0)
        assert cap_reposo == "REPOSO_SILICIO"
    
    def test_analizar_familia_curvas(self):
        """Test curve family analysis."""
        familia = [
            {'rango_adelico': 1, 'L_E1': 0.0},
            {'rango_adelico': 2, 'L_E1': 0.0},
            {'rango_adelico': 1, 'L_E1': 0.5},
        ]
        
        analisis = analizar_familia_curvas(familia)
        
        assert analisis['num_curvas'] == 3
        assert analisis['rango_promedio'] == (1 + 2 + 1) / 3
        assert analisis['rango_maximo'] == 2
        assert analisis['superfluidos'] == 2  # Two with L_E1=0
        assert 0 <= analisis['psi_promedio'] <= 1
    
    def test_analizar_familia_curvas_vacia(self):
        """Test analysis with empty family."""
        analisis = analizar_familia_curvas([])
        
        assert analisis['num_curvas'] == 0
        assert analisis['rango_promedio'] == 0.0


# ============================================================================
# TEST RUNNER
# ============================================================================

def run_tests():
    """Run all tests with custom test runner (matching repo pattern)."""
    import traceback
    
    print("=" * 75)
    print(" " * 20 + "BSD ADÉLICO CONNECTOR TESTS")
    print(" " * 15 + "Pentágono Logos Validation Suite")
    print("=" * 75)
    print()
    
    test_classes = [
        TestCodificadorADNRiemann,
        TestBSDConnector,
        TestPentagonoValidacion,
        TestUtilityFunctions
    ]
    
    total_tests = 0
    passed_tests = 0
    failed_tests = []
    
    for test_class in test_classes:
        print(f"\n{test_class.__name__}:")
        print("-" * 75)
        
        test_instance = test_class()
        test_methods = [m for m in dir(test_instance) if m.startswith('test_')]
        
        for method_name in test_methods:
            total_tests += 1
            try:
                method = getattr(test_instance, method_name)
                method()
                print(f"  ✓ {method_name}")
                passed_tests += 1
            except AssertionError as e:
                print(f"  ✗ {method_name}: {e}")
                failed_tests.append((test_class.__name__, method_name, str(e)))
            except Exception as e:
                print(f"  ✗ {method_name}: {type(e).__name__}: {e}")
                failed_tests.append((test_class.__name__, method_name, f"{type(e).__name__}: {e}"))
    
    # Summary
    print("\n" + "=" * 75)
    print(f"Test Results: {passed_tests}/{total_tests} passed")
    
    if failed_tests:
        print("\nFailed tests:")
        for class_name, method_name, error in failed_tests:
            print(f"  • {class_name}.{method_name}: {error}")
        print("=" * 75)
        return False
    else:
        print("\n✓ All tests passed! Pentagon Logos operational.")
        print("  Bóveda del Logos: CERRADA ∴𓂀Ω∞³")
        print("=" * 75)
        return True


if __name__ == "__main__":
    import sys
    success = run_tests()
    sys.exit(0 if success else 1)
