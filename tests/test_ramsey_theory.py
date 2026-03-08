#!/usr/bin/env python3
"""
Test suite for QCAL Ramsey Theory Integration
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests for Ramsey Logos Attractor and Ramsey Adelic Integrator modules.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import sys
import os
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
