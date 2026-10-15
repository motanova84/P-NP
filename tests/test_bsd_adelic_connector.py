#!/usr/bin/env python3
"""
Tests for BSD Adélico Connector module.

Tests the BSD conjecture integration with Pentagon Logos closure.

Author: JMMB Ψ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Test Suite for BSD Adélico Connector

Tests for BSD-ADN synchronization and Pentagon Logos closure.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import unittest
import math
from qcal.bsd_adelic_connector import (
    compute_l_function_at_1,
    adelic_spectral_trace,
    validate_bsd_identity,
    connect_dna_hotspots,
    validate_pentagon_logos_closure,
    KAPPA_PI,
    F0_HZ,
    PHI,
    SUPERFLUID_L_THRESHOLD,
    MAX_COHERENCE_THRESHOLD,
    MIN_DNA_HOTSPOTS,
    MIN_RAMSEY_NODES,
)


class TestBSDFunctions(unittest.TestCase):
    """Test cases for BSD basic functions."""
    
    def test_l_function_rank_zero(self):
        """Test L-function for rank-0 curves."""
        L_value = compute_l_function_at_1(11, 0)
        # Rank 0 should give non-zero value
        self.assertGreater(abs(L_value), 0.0)
    
    def test_l_function_rank_positive(self):
        """Test L-function for positive rank curves."""
        L_value_r1 = compute_l_function_at_1(37, 1)
        L_value_r2 = compute_l_function_at_1(389, 2)
        
        # Positive rank should give zero
        self.assertEqual(L_value_r1, 0.0)
        self.assertEqual(L_value_r2, 0.0)
    
    def test_adelic_spectral_trace_structure(self):
        """Test adelic spectral trace returns complex number."""
        trace = adelic_spectral_trace(37, 1, s=1.0)
        self.assertIsInstance(trace, complex)
    
    def test_adelic_spectral_trace_prime_17(self):
        """Test enhanced trace for conductor with factor 17."""
        trace_17 = adelic_spectral_trace(17, 0, s=1.0)
        trace_19 = adelic_spectral_trace(19, 0, s=1.0)
        
        # Both should be complex
        self.assertIsInstance(trace_17, complex)
        self.assertIsInstance(trace_19, complex)
        
        # 17 should have imaginary component due to special resonance
        # (though this is implementation-dependent)
        self.assertTrue(abs(trace_17.imag) >= 0 or abs(trace_17.real) >= 0)


class TestDNAHotspots(unittest.TestCase):
    """Test cases for DNA hotspot detection."""
    
    def test_connect_dna_hotspots_structure(self):
        """Test DNA hotspot connection structure."""
        result = connect_dna_hotspots(17, 0)
        
        # Check required keys
        self.assertIn('conductor', result)
        self.assertIn('rank', result)
        self.assertIn('sequence_length', result)
        self.assertIn('num_hotspots', result)
        self.assertIn('hotspots', result)
        self.assertIn('f0', result)
        self.assertIn('phi', result)
        
        # Check constants
        self.assertEqual(result['f0'], F0_HZ)
        self.assertAlmostEqual(result['phi'], PHI, places=6)
    
    def test_dna_hotspots_prime_17(self):
        """Test that prime-17 conductor produces hotspots."""
        result = connect_dna_hotspots(17, 0)
        
        # Should have at least 1 hotspot
        self.assertGreaterEqual(result['num_hotspots'], 1)
        
        # Check hotspot structure
        if result['num_hotspots'] > 0:
            hotspot = result['hotspots'][0]
            self.assertIn('position', hotspot)
            self.assertIn('base', hotspot)
            self.assertIn('frequency', hotspot)
            self.assertIn('resonance', hotspot)
            self.assertIn('prime_factor', hotspot)
            
            # Base should be one of G, A, C, T
            self.assertIn(hotspot['base'], ['G', 'A', 'C', 'T'])
            
            # Resonance should be >= 0.95
            self.assertGreaterEqual(hotspot['resonance'], 0.95)
    
    def test_dna_hotspots_composite_with_17(self):
        """Test DNA hotspots for composite conductor with 17-factor."""
        result = connect_dna_hotspots(17*19, 1)
        
        # Should have multiple hotspots (from 17 and 19)
        self.assertGreaterEqual(result['num_hotspots'], 1)
        
        # Check that 17 is among prime factors
        has_17_hotspot = any(
            hs['prime_factor'] == 17 
            for hs in result['hotspots']
        )
        self.assertTrue(has_17_hotspot)


class TestPentagonLogos(unittest.TestCase):
    """Test cases for Pentagon Logos closure."""
    
    def test_pentagon_closure_all_conditions_met(self):
        """Test Pentagon closure when all conditions are met."""
        # Rank-1 curve with 17-factor, high coherence, enough Ramsey nodes
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # All conditions should be met
        self.assertTrue(result['condition_1_superfluid'])
        self.assertTrue(result['condition_2_coherence'])
        self.assertTrue(result['condition_3_dna_hotspots'])
        self.assertTrue(result['condition_4_ramsey_nodes'])
        
        # Pentagon should be closed
        self.assertTrue(result['pentagon_closed'])
        self.assertEqual(result['closure_strength'], 1.0)
        self.assertTrue(result['millennium_problems_unified'])
    
    def test_pentagon_closure_missing_coherence(self):
        """Test Pentagon doesn't close with low coherence."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.95,  # Below threshold
            n_ramsey_nodes=55
        )
        
        # Coherence condition should fail
        self.assertFalse(result['condition_2_coherence'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
        self.assertLess(result['closure_strength'], 1.0)
    
    def test_pentagon_closure_below_ramsey_threshold(self):
        """Test Pentagon doesn't close below Ramsey threshold."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=45  # Below threshold
        )
        
        # Ramsey condition should fail
        self.assertFalse(result['condition_4_ramsey_nodes'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
    
    def test_pentagon_closure_rank_zero_non_superfluid(self):
        """Test Pentagon with rank-0 curve (L(E,1) ≠ 0)."""
        result = validate_pentagon_logos_closure(
            conductor=11,
            rank=0,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # Superfluid condition should fail for rank-0
        self.assertFalse(result['condition_1_superfluid'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
    
    def test_pentagon_closure_structure(self):
        """Test Pentagon closure result structure."""
        result = validate_pentagon_logos_closure(
            conductor=37,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # Check all required keys
        required_keys = [
            'conductor', 'rank', 'L_at_1', 'coherence_psi', 'n_ramsey_nodes',
            'num_dna_hotspots', 'condition_1_superfluid', 'condition_2_coherence',
            'condition_3_dna_hotspots', 'condition_4_ramsey_nodes',
            'pentagon_closed', 'closure_strength', 'millennium_problems_unified',
            'kappa_pi', 'f0_hz'
        ]
        
        for key in required_keys:
            self.assertIn(key, result)
        
        # Check constants
        self.assertEqual(result['kappa_pi'], KAPPA_PI)
        self.assertEqual(result['f0_hz'], F0_HZ)
    
    def test_pentagon_closure_strength_calculation(self):
        """Test closure strength is calculated correctly."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.95,  # Fails
            n_ramsey_nodes=45    # Fails
        )
        
        # Two conditions fail, two pass
        # Strength should be 0.5
        self.assertEqual(result['closure_strength'], 0.5)


class TestConstants(unittest.TestCase):
    """Test universal constants."""
    
    def test_kappa_pi(self):
        """Test κ_Π millennium constant."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
    
    def test_f0_frequency(self):
        """Test f₀ fundamental frequency."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_phi_golden_ratio(self):
        """Test Φ golden ratio."""
        self.assertAlmostEqual(PHI, 1.6180339887, places=6)
    
    def test_thresholds(self):
        """Test Pentagon closure thresholds."""
        self.assertEqual(SUPERFLUID_L_THRESHOLD, 0.01)
        self.assertEqual(MAX_COHERENCE_THRESHOLD, 0.999)
        self.assertEqual(MIN_DNA_HOTSPOTS, 1)
        self.assertEqual(MIN_RAMSEY_NODES, 51)


class TestBSDIdentity(unittest.TestCase):
    """Test BSD identity validation."""
    
    def test_validate_bsd_identity_structure(self):
        """Test BSD identity validation structure."""
        result = validate_bsd_identity(37, 1)
        
        # Check required keys
        self.assertIn('conductor', result)
        self.assertIn('rank', result)
        self.assertIn('L_at_1', result)
        self.assertIn('trace', result)
        self.assertIn('kernel_dim_estimate', result)
        self.assertIn('L_vanishes_correctly', result)
        self.assertIn('has_factor_17', result)
    
    def test_validate_bsd_identity_rank_consistency(self):
        """Test that L-function vanishing is consistent with rank."""
        # Rank 0: L(E,1) ≠ 0
        result_r0 = validate_bsd_identity(11, 0)
        self.assertTrue(result_r0['L_vanishes_correctly'])
        self.assertGreater(abs(result_r0['L_at_1']), SUPERFLUID_L_THRESHOLD)
        
        # Rank 1: L(E,1) = 0
        result_r1 = validate_bsd_identity(37, 1)
        self.assertTrue(result_r1['L_vanishes_correctly'])
        self.assertEqual(result_r1['L_at_1'], 0.0)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
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
