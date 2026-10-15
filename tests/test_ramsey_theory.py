#!/usr/bin/env python3
"""
Tests for Ramsey Logos Attractor module.

Tests the Ramsey theory integration into QCAL at 51-node threshold.

Author: JMMB Ψ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Test suite for QCAL Ramsey Theory Integration
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests for Ramsey Logos Attractor and Ramsey Adelic Integrator modules.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import unittest
import math
from qcal.ramsey_logos_attractor import (
    coherencia_ramsey,
    emergencia_ramsey_qcal,
    ramsey_number_estimate,
    compute_ramsey_logos_field,
    validate_ramsey_threshold,
    RAMSEY_THRESHOLD,
    KAPPA_PI,
    F0_HZ,
    LOGISTIC_K,
    LOGISTIC_X0,
)


class TestRamseyLogosAttractor(unittest.TestCase):
    """Test cases for Ramsey Logos Attractor."""
    
    def test_coherencia_ramsey_threshold(self):
        """Test coherence at exact threshold."""
        coherence = coherencia_ramsey(RAMSEY_THRESHOLD)
        # At threshold, coherence should be high (near 0.99)
        self.assertGreater(coherence, 0.98)
        self.assertLess(coherence, 1.0)
    
    def test_coherencia_ramsey_below_threshold(self):
        """Test coherence below threshold."""
        coherence_low = coherencia_ramsey(10)
        coherence_mid = coherencia_ramsey(40)
        
        # Should be much lower than threshold
        self.assertLess(coherence_low, 0.1)
        self.assertLess(coherence_mid, coherencia_ramsey(RAMSEY_THRESHOLD))
    
    def test_coherencia_ramsey_above_threshold(self):
        """Test coherence above threshold."""
        coherence_60 = coherencia_ramsey(60)
        coherence_100 = coherencia_ramsey(100)
        
        # Should approach 1.0 above threshold
        self.assertGreater(coherence_60, 0.999)
        self.assertGreater(coherence_100, 0.9999)
    
    def test_coherencia_ramsey_monotonic(self):
        """Test that coherence increases monotonically."""
        prev_coherence = 0.0
        for n in range(10, 100, 5):
            coherence = coherencia_ramsey(n)
            self.assertGreaterEqual(coherence, prev_coherence)
            prev_coherence = coherence
    
    def test_emergencia_ramsey_qcal_structure(self):
        """Test structure of emergencia_ramsey_qcal output."""
        result = emergencia_ramsey_qcal(51)
        
        # Check required keys
        self.assertIn('n_nodos', result)
        self.assertIn('coherencia', result)
        self.assertIn('orden_garantizado', result)
        self.assertIn('umbral_alcanzado', result)
        self.assertIn('distancia_umbral', result)
        self.assertIn('kappa_pi', result)
        self.assertIn('frecuencia_base', result)
        
        # Check values
        self.assertEqual(result['n_nodos'], 51)
        self.assertEqual(result['umbral_ramsey'], RAMSEY_THRESHOLD)
        self.assertEqual(result['kappa_pi'], KAPPA_PI)
        self.assertEqual(result['frecuencia_base'], F0_HZ)
    
    def test_emergencia_order_guarantee(self):
        """Test order guarantee at and above threshold."""
        # Below threshold
        result_below = emergencia_ramsey_qcal(50)
        self.assertFalse(result_below['orden_garantizado'])
        
        # At threshold
        result_at = emergencia_ramsey_qcal(51)
        self.assertTrue(result_at['orden_garantizado'])
        
        # Above threshold
        result_above = emergencia_ramsey_qcal(60)
        self.assertTrue(result_above['orden_garantizado'])
    
    def test_emergencia_kappa_factor(self):
        """Test kappa factor integration."""
        # Below threshold: should be 0
        result_below = emergencia_ramsey_qcal(40)
        self.assertEqual(result_below['kappa_factor'], 0.0)
        
        # At threshold: should be positive
        result_at = emergencia_ramsey_qcal(51)
        self.assertGreater(result_at['kappa_factor'], 0.0)
        
        # Should be approximately coherencia * KAPPA_PI
        expected = result_at['coherencia'] * KAPPA_PI
        self.assertAlmostEqual(result_at['kappa_factor'], expected, places=6)
    
    def test_ramsey_number_estimate_base_cases(self):
        """Test Ramsey number estimates for base cases."""
        self.assertEqual(ramsey_number_estimate(1, 5), 1)
        self.assertEqual(ramsey_number_estimate(5, 1), 1)
        self.assertEqual(ramsey_number_estimate(2, 5), 5)
        self.assertEqual(ramsey_number_estimate(5, 2), 5)
    
    def test_ramsey_number_estimate_known_values(self):
        """Test known Ramsey numbers."""
        self.assertEqual(ramsey_number_estimate(3, 3), 6)
        self.assertEqual(ramsey_number_estimate(3, 4), 9)
        self.assertEqual(ramsey_number_estimate(4, 4), 18)
    
    def test_compute_ramsey_logos_field_structure(self):
        """Test Ramsey Logos field computation structure."""
        result = compute_ramsey_logos_field(51)
        
        # Check required keys
        self.assertIn('n_nodos', result)
        self.assertIn('coherencia', result)
        self.assertIn('field_strength', result)
        self.assertIn('basin_depth', result)
        self.assertIn('resonance', result)
        self.assertIn('phase_rad', result)
    
    def test_compute_ramsey_logos_field_basin_depth(self):
        """Test attractor basin depth behavior."""
        # Below threshold: shallow basin
        result_below = compute_ramsey_logos_field(40)
        self.assertLess(result_below['basin_depth'], 0.5)
        
        # At threshold: deep basin
        result_at = compute_ramsey_logos_field(51)
        self.assertEqual(result_at['basin_depth'], 1.0)
        
        # Above threshold: deep basin
        result_above = compute_ramsey_logos_field(60)
        self.assertEqual(result_above['basin_depth'], 1.0)
    
    def test_validate_ramsey_threshold(self):
        """Test validation of Ramsey threshold."""
        validation = validate_ramsey_threshold()
        
        # Check structure
        self.assertIn('threshold', validation)
        self.assertIn('threshold_coherence', validation)
        self.assertIn('monotonic', validation)
        self.assertIn('order_correct', validation)
        self.assertIn('validation_passed', validation)
        
        # Check values
        self.assertEqual(validation['threshold'], RAMSEY_THRESHOLD)
        self.assertTrue(validation['monotonic'])
        self.assertTrue(validation['order_correct'])
        self.assertTrue(validation['validation_passed'])
        
        # Coherence at threshold should be > 0.95
        self.assertGreater(validation['threshold_coherence'], 0.95)
    
    def test_logistic_parameters(self):
        """Test logistic function parameters are correct."""
        self.assertEqual(LOGISTIC_K, 17)
        self.assertAlmostEqual(LOGISTIC_X0, 0.72, places=2)
    
    def test_constants(self):
        """Test universal constants."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
        self.assertEqual(RAMSEY_THRESHOLD, 51)
    
    def test_coherencia_ramsey_edge_cases(self):
        """Test edge cases for coherence function."""
        # Zero nodes
        self.assertEqual(coherencia_ramsey(0), 0.0)
        
        # Negative nodes (should return 0)
        self.assertEqual(coherencia_ramsey(-5), 0.0)
        
        # Very large number of nodes
        coherence_large = coherencia_ramsey(1000)
        self.assertAlmostEqual(coherence_large, 1.0, places=10)


class TestRamseyIntegration(unittest.TestCase):
    """Integration tests for Ramsey theory with QCAL."""
    
    def test_ramsey_qcal_coupling(self):
        """Test coupling between Ramsey coherence and κ_Π."""
        result = emergencia_ramsey_qcal(60)
        
        # Kappa factor should couple coherence with millennium constant
        expected_kappa = result['coherencia'] * KAPPA_PI
        self.assertAlmostEqual(result['kappa_factor'], expected_kappa, places=6)
    
    def test_threshold_transition_smoothness(self):
        """Test smooth transition around threshold."""
        # Get coherence values around threshold
        coherences = []
        for n in range(48, 55):
            result = emergencia_ramsey_qcal(n)
            coherences.append(result['coherencia'])
        
        # Check smooth transition (no jumps)
        for i in range(len(coherences) - 1):
            diff = coherences[i+1] - coherences[i]
            self.assertGreater(diff, 0)  # Increasing
            self.assertLess(diff, 0.1)  # Not too steep
    
    def test_ramsey_logos_field_consistency(self):
        """Test consistency between different Ramsey functions."""
        n = 55
        
        # Get coherence from basic function
        coherence_basic = coherencia_ramsey(n)
        
        # Get coherence from emergence function
        result_emergence = emergencia_ramsey_qcal(n)
        coherence_emergence = result_emergence['coherencia']
        
        # Get coherence from field function
        result_field = compute_ramsey_logos_field(n)
        coherence_field = result_field['coherencia']
        
        # All should match
        self.assertAlmostEqual(coherence_basic, coherence_emergence, places=10)
        self.assertAlmostEqual(coherence_basic, coherence_field, places=10)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import modules to test
from qcal.ramsey_logos_attractor import emergencia_ramsey_qcal, escanear_orden_ramsey_bsd, NODOS_LOGOS
from qcal.ramsey_adelic_integrator import integrar_ramsey_bsd, generar_certificado_ramsey_bsd


class TestRamseyLogosAttractor(unittest.TestCase):
    """Test cases for Ramsey Logos Attractor module."""
    
    def test_emergencia_ramsey_bajo_umbral(self):
        """Test Ramsey emergence below threshold (< 51 nodes)."""
        resultado = emergencia_ramsey_qcal(30)
        
        self.assertEqual(resultado['ramsey_status'], 'CAOS_TRANSITORIO')
        self.assertFalse(resultado['logos_manifestado'])
        self.assertEqual(resultado['nodos_critico'], NODOS_LOGOS)
        self.assertIsInstance(resultado['psi_emergencia'], float)
        self.assertGreaterEqual(resultado['psi_emergencia'], 0.0)
        self.assertLessEqual(resultado['psi_emergencia'], 1.0)
    
    def test_emergencia_ramsey_umbral_exacto(self):
        """Test Ramsey emergence at exact threshold (51 nodes)."""
        resultado = emergencia_ramsey_qcal(51)
        
        self.assertEqual(resultado['ramsey_status'], 'ORDEN_INEVITABLE')
        self.assertTrue(resultado['logos_manifestado'])
        self.assertEqual(resultado['nodos_critico'], 51)
    
    def test_emergencia_ramsey_sobre_umbral(self):
        """Test Ramsey emergence above threshold (> 51 nodes)."""
        resultado = emergencia_ramsey_qcal(100)
        
        self.assertEqual(resultado['ramsey_status'], 'ORDEN_INEVITABLE')
        self.assertTrue(resultado['logos_manifestado'])
        self.assertGreaterEqual(resultado['psi_emergencia'], 0.999)
    
    def test_emergencia_ramsey_nodos_cero(self):
        """Test Ramsey emergence with zero nodes."""
        resultado = emergencia_ramsey_qcal(0)
        
        self.assertEqual(resultado['ramsey_status'], 'CAOS_TRANSITORIO')
        self.assertFalse(resultado['logos_manifestado'])
    
    def test_escanear_orden_ramsey_bsd_rango_positivo(self):
        """Test Ramsey-BSD scan with positive BSD rank."""
        curva = {'rango_adelico': 1}
        resultado = escanear_orden_ramsey_bsd(curva, "GACT")
        
        self.assertEqual(resultado['status'], 'ORDEN_MANIFESTADO')
        self.assertEqual(resultado['nodo_central'], 'GACT')
        self.assertAlmostEqual(resultado['coherencia_ramsey'], 0.999999, places=5)
        self.assertEqual(resultado['conexion_bsd'], 'VALIDADA')
        self.assertGreater(resultado['hotspots_adn'], 0)
    
    def test_escanear_orden_ramsey_bsd_rango_cero(self):
        """Test Ramsey-BSD scan with zero BSD rank."""
        curva = {'rango_adelico': 0}
        resultado = escanear_orden_ramsey_bsd(curva, "GACT")
        
        self.assertEqual(resultado['status'], 'ESPERA')
        self.assertIsNone(resultado['nodo_central'])
        self.assertAlmostEqual(resultado['coherencia_ramsey'], 0.888, places=3)
        self.assertEqual(resultado['conexion_bsd'], 'REPOSO')
    
    def test_escanear_diferentes_secuencias(self):
        """Test scanning different DNA sequences."""
        curva = {'rango_adelico': 1}
        secuencias = ["GACT", "CGTA", "ATCG", "AAAA"]
        
        for seq in secuencias:
            resultado = escanear_orden_ramsey_bsd(curva, seq)
            self.assertEqual(resultado['status'], 'ORDEN_MANIFESTADO')
            self.assertEqual(resultado['nodo_central'], seq)


class TestRamseyAdelicIntegrator(unittest.TestCase):
    """Test cases for Ramsey Adelic Integrator module."""
    
    def test_integrar_ramsey_bsd_basico(self):
        """Test basic Ramsey-BSD integration."""
        grafo_info = ["GACT", "CGTA", "ATCG"] * 20  # 60 nodes
        curva = {'rango_adelico': 1}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        
        self.assertEqual(resultado['n_nodos'], 60)
        self.assertEqual(resultado['ramsey_estado'], 'ORDEN_INEVITABLE')
        self.assertTrue(resultado['logos_manifestado'])
        self.assertGreater(resultado['coherencia_global'], 0.99)
        self.assertEqual(resultado['rango_bsd'], 1)
        self.assertEqual(len(resultado['subgrafos_orden']), 60)
    
    def test_integrar_ramsey_bsd_bajo_umbral(self):
        """Test Ramsey-BSD integration below threshold."""
        grafo_info = ["GACT"] * 30  # 30 nodes
        curva = {'rango_adelico': 1}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        
        self.assertEqual(resultado['n_nodos'], 30)
        self.assertEqual(resultado['ramsey_estado'], 'CAOS_TRANSITORIO')
        self.assertFalse(resultado['logos_manifestado'])
    
    def test_integrar_ramsey_bsd_sin_rango(self):
        """Test Ramsey-BSD integration without BSD rank."""
        grafo_info = ["GACT"] * 60
        curva = {'rango_adelico': 0}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        
        self.assertEqual(resultado['rango_bsd'], 0)
        self.assertFalse(resultado['certificado_milenio']['bsd'])
        self.assertFalse(resultado['certificado_milenio']['unificacion'])
    
    def test_certificado_milenio_completo(self):
        """Test complete Millennium certification."""
        grafo_info = ["GACT"] * 60
        curva = {'rango_adelico': 1}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        
        cert = resultado['certificado_milenio']
        self.assertTrue(cert['ramsey'])
        self.assertTrue(cert['bsd'])
        self.assertTrue(cert['unificacion'])
    
    def test_generar_certificado_ramsey_bsd(self):
        """Test certificate generation."""
        grafo_info = ["GACT", "CGTA", "ATCG"]
        curva = {'rango_adelico': 1}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        certificado = generar_certificado_ramsey_bsd(resultado)
        
        self.assertIsInstance(certificado, str)
        self.assertIn("CERTIFICADO RAMSEY-BSD QCAL", certificado)
        self.assertIn("ORDEN INEVITABLE", certificado)
        self.assertIn("Logos Manifestado", certificado)
        self.assertIn("Coherencia Global", certificado)
    
    def test_coherencia_global_calculo(self):
        """Test global coherence calculation."""
        grafo_info = ["GACT", "ATCG"] * 30  # Mixed sequences
        curva = {'rango_adelico': 1}
        
        resultado = integrar_ramsey_bsd(grafo_info, curva)
        
        # All sequences should have high coherence with BSD rank > 0
        self.assertGreater(resultado['coherencia_global'], 0.99)


class TestRamseyConstants(unittest.TestCase):
    """Test constants and thresholds."""
    
    def test_nodos_logos_constante(self):
        """Test that NODOS_LOGOS is 51."""
        self.assertEqual(NODOS_LOGOS, 51)
    
    def test_f0_frecuencia(self):
        """Test that F0 frequency is correctly defined."""
        from qcal.ramsey_logos_attractor import F0
        self.assertAlmostEqual(F0, 141.7001, places=4)


def run_tests():
    """Run all tests with custom output."""
    print("=" * 80)
    print("QCAL Ramsey Theory - Test Suite")
    print("=" * 80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestRamseyLogosAttractor))
    suite.addTests(loader.loadTestsFromTestCase(TestRamseyAdelicIntegrator))
    suite.addTests(loader.loadTestsFromTestCase(TestRamseyConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 80)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print(f"✓ {result.testsRun} tests executed successfully")
        print("✓ Ramsey Order Inevitable at Node 51")
        print("✓ BSD Integration Validated")
    else:
        print("✗ SOME TESTS FAILED")
        print(f"✗ Failures: {len(result.failures)}")
        print(f"✗ Errors: {len(result.errors)}")
    print("=" * 80)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
