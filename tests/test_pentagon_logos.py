#!/usr/bin/env python3
"""
Test suite for ADN-Riemann and BSD Adélico modules
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests for Pentagon Logos integration modules.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
"""

import sys
import os
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from qcal.adn_riemann import CodificadorADNRiemann, generar_secuencia_resonante, comparar_secuencias
from qcal.bsd_adelic_connector import BSDAdelicoConnector


class TestCodificadorADNRiemann(unittest.TestCase):
    """Test cases for CodificadorADNRiemann."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.codificador = CodificadorADNRiemann()
    
    def test_inicializacion(self):
        """Test initialization of encoder."""
        self.assertIsInstance(self.codificador, CodificadorADNRiemann)
        self.assertEqual(self.codificador.secuencia_actual, "")
        self.assertEqual(self.codificador.frecuencias, [])
        self.assertEqual(self.codificador.hotspots, [])
    
    def test_frecuencias_base(self):
        """Test that base frequencies are correctly defined."""
        self.assertIn('G', self.codificador.FRECUENCIAS_BASE)
        self.assertIn('A', self.codificador.FRECUENCIAS_BASE)
        self.assertIn('C', self.codificador.FRECUENCIAS_BASE)
        self.assertIn('T', self.codificador.FRECUENCIAS_BASE)
        self.assertIn('U', self.codificador.FRECUENCIAS_BASE)
        
        # G debe ser f₀
        self.assertAlmostEqual(self.codificador.FRECUENCIAS_BASE['G'], 141.7001, places=4)
    
    def test_codificar_secuencia_simple(self):
        """Test encoding a simple sequence."""
        frecuencias = self.codificador.codificar("GACT")
        self.assertEqual(len(frecuencias), 4)
        self.assertGreater(frecuencias[0], 0)  # G
        self.assertGreater(frecuencias[1], 0)  # A
        self.assertGreater(frecuencias[2], 0)  # C
        self.assertGreater(frecuencias[3], 0)  # T
    
    def test_calcular_resonancia(self):
        """Test resonance calculation."""
        # Frecuencia f₀ debe tener resonancia máxima
        f0 = self.codificador.FRECUENCIAS_BASE['G']
        resonancia = self.codificador.calcular_resonancia(f0, f0)
        self.assertGreaterEqual(resonancia, 0.9)  # Muy alta resonancia
        
        # Frecuencia muy diferente debe tener baja resonancia
        resonancia_baja = self.codificador.calcular_resonancia(1000, f0)
        self.assertLess(resonancia_baja, resonancia)
    
    def test_identificar_hotspots_gact(self):
        """Test hotspot identification for GACT sequence."""
        hotspots = self.codificador.identificar_hotspots("GACT")
        self.assertIsInstance(hotspots, list)
        self.assertGreater(len(hotspots), 0)  # Should have at least one hotspot
        self.assertIn(0, hotspots)  # G at position 0 should be a hotspot
    
    def test_identificar_hotspots_gggg(self):
        """Test hotspot identification for GGGG sequence."""
        hotspots = self.codificador.identificar_hotspots("GGGG")
        self.assertEqual(len(hotspots), 4)  # All G's are hotspots
    
    def test_analizar_secuencia_completo(self):
        """Test complete sequence analysis."""
        analisis = self.codificador.analizar_secuencia("GACT")
        
        self.assertIn('secuencia', analisis)
        self.assertIn('longitud', analisis)
        self.assertIn('frecuencias', analisis)
        self.assertIn('hotspots', analisis)
        self.assertIn('n_hotspots', analisis)
        self.assertIn('resonancia_promedio', analisis)
        self.assertIn('conteo_bases', analisis)
        self.assertIn('coherencia_cuantica', analisis)
        self.assertIn('psi', analisis)
        
        self.assertEqual(analisis['secuencia'], "GACT")
        self.assertEqual(analisis['longitud'], 4)
        self.assertGreaterEqual(analisis['psi'], 0.0)
        self.assertLessEqual(analisis['psi'], 1.0)
    
    def test_secuencia_optima(self):
        """Test optimal sequence generation."""
        opt = self.codificador.secuencia_optima(4)
        self.assertEqual(len(opt), 4)
        self.assertEqual(opt, "GACT")  # Known optimal 4-base sequence
    
    def test_espectro_frecuencias(self):
        """Test frequency spectrum calculation."""
        espectro = self.codificador.espectro_frecuencias("GACT")
        
        self.assertIn('frecuencia_fundamental', espectro)
        self.assertIn('frecuencia_maxima', espectro)
        self.assertIn('frecuencia_promedio', espectro)
        self.assertIn('ancho_banda', espectro)
        
        self.assertGreater(espectro['frecuencia_maxima'], espectro['frecuencia_fundamental'])


class TestBSDAdelicoConnector(unittest.TestCase):
    """Test cases for BSDAdelicoConnector."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.connector = BSDAdelicoConnector()
        self.curva_mordell = {
            'nombre': 'Curva de Mordell',
            'rango_adelico': 1,
            'ecuacion': 'y² = x³ + 1'
        }
        self.curva_rango_0 = {
            'nombre': 'Curva Rango 0',
            'rango_adelico': 0
        }
    
    def test_inicializacion(self):
        """Test initialization of connector."""
        self.assertIsInstance(self.connector, BSDAdelicoConnector)
        self.assertIsInstance(self.connector.codificador_adn, CodificadorADNRiemann)
    
    def test_calcular_l_function_rango_positivo(self):
        """Test L-function calculation for positive rank."""
        l_e1 = self.connector.calcular_l_function(self.curva_mordell, 1.0)
        self.assertEqual(l_e1, 0.0)  # Should be zero for rank > 0
    
    def test_calcular_l_function_rango_cero(self):
        """Test L-function calculation for rank zero."""
        l_e1 = self.connector.calcular_l_function(self.curva_rango_0, 1.0)
        self.assertGreater(l_e1, 0.0)  # Should be non-zero for rank = 0
    
    def test_verificar_bsd_rango_positivo(self):
        """Test BSD verification for positive rank."""
        bsd = self.connector.verificar_bsd(self.curva_mordell)
        
        self.assertEqual(bsd['rango'], 1)
        self.assertEqual(bsd['l_e1'], 0.0)
        self.assertEqual(bsd['orden_cero'], 1)
        self.assertTrue(bsd['bsd_verificado'])
        self.assertTrue(bsd['flujo_superfluido'])
        self.assertEqual(bsd['estado'], 'SUPERFLUIDO')
    
    def test_verificar_bsd_rango_cero(self):
        """Test BSD verification for rank zero."""
        bsd = self.connector.verificar_bsd(self.curva_rango_0)
        
        self.assertEqual(bsd['rango'], 0)
        self.assertGreater(bsd['l_e1'], 0.0)
        self.assertFalse(bsd['flujo_superfluido'])
        self.assertEqual(bsd['estado'], 'VISCOSO')
    
    def test_conectar_bsd_adn_correspondencia(self):
        """Test BSD-ADN connection with correspondence."""
        conexion = self.connector.conectar_bsd_adn(self.curva_mordell, "GACT")
        
        self.assertIn('bsd', conexion)
        self.assertIn('adn', conexion)
        self.assertIn('conexion', conexion)
        
        # Should have at least one hotspot
        self.assertGreaterEqual(conexion['adn']['n_hotspots'], 1)
        
        # Coherence should be high for superfluid with hotspots
        self.assertGreaterEqual(conexion['conexion']['coherencia_sistema'], 0.95)
    
    def test_validar_pentagono_logos_cerrado(self):
        """Test Pentagon Logos validation for closed state."""
        validacion = self.connector.validar_pentagono_logos(
            self.curva_mordell, 
            "GACT", 
            60  # > 51 nodes
        )
        
        self.assertIn('pentagono_logos', validacion)
        self.assertIn('condiciones', validacion)
        self.assertIn('coherencia_global', validacion)
        self.assertIn('pentagono_cerrado', validacion)
        self.assertIn('boveda_verdad', validacion)
        
        # Check conditions
        conds = validacion['condiciones']
        self.assertTrue(conds['1_superfluido'])  # L(E,1) = 0
        self.assertTrue(conds['4_ramsey_orden'])  # nodos >= 51
        
        # Pentagon should be closed if all conditions met
        if all(conds.values()):
            self.assertTrue(validacion['pentagono_cerrado'])
            self.assertEqual(validacion['boveda_verdad'], 'CERRADA')
    
    def test_validar_pentagono_logos_abierto(self):
        """Test Pentagon Logos validation for open state."""
        validacion = self.connector.validar_pentagono_logos(
            self.curva_rango_0,  # rank 0 → no superfluid
            "ATCATC",  # no G
            30  # < 51 nodes
        )
        
        # Should not be fully closed
        conds = validacion['condiciones']
        self.assertFalse(conds['1_superfluido'])  # L(E,1) != 0
        self.assertFalse(conds['4_ramsey_orden'])  # nodos < 51
        
        self.assertFalse(validacion['pentagono_cerrado'])
        self.assertEqual(validacion['boveda_verdad'], 'ABIERTA')
    
    def test_generar_certificado_pentagono(self):
        """Test Pentagon certificate generation."""
        validacion = self.connector.validar_pentagono_logos(
            self.curva_mordell, 
            "GACT", 
            60
        )
        
        certificado = self.connector.generar_certificado_pentagono(validacion)
        
        self.assertIsInstance(certificado, str)
        self.assertIn("CERTIFICADO PENTÁGONO DEL LOGOS", certificado)
        self.assertIn("f₀", certificado)
        self.assertIn("ADN (Biología)", certificado)
        self.assertIn("Riemann (Estructura)", certificado)
        self.assertIn("Navier-Stokes (Dinámica)", certificado)
        self.assertIn("P vs NP (Lógica)", certificado)
        self.assertIn("BSD (Aritmética)", certificado)
        self.assertIn("Ramsey (Combinatoria)", certificado)


class TestUtilityFunctions(unittest.TestCase):
    """Test utility functions."""
    
    def test_generar_secuencia_resonante(self):
        """Test resonant sequence generation."""
        seq = generar_secuencia_resonante(100, 0.4)
        self.assertEqual(len(seq), 100)
        
        # Should have approximately 40% G
        n_g = seq.count('G')
        self.assertGreaterEqual(n_g, 35)
        self.assertLessEqual(n_g, 45)
    
    def test_comparar_secuencias(self):
        """Test sequence comparison."""
        comparacion = comparar_secuencias("GACT", "ATCG")
        
        self.assertIn('secuencia_1', comparacion)
        self.assertIn('secuencia_2', comparacion)
        self.assertIn('mejor', comparacion)
        self.assertIn('diferencia_psi', comparacion)
        
        self.assertIn(comparacion['mejor'], ["GACT", "ATCG"])


def run_tests():
    """Run all tests with custom output."""
    print("=" * 80)
    print("QCAL Pentagon Logos - Test Suite")
    print("=" * 80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCodificadorADNRiemann))
    suite.addTests(loader.loadTestsFromTestCase(TestBSDAdelicoConnector))
    suite.addTests(loader.loadTestsFromTestCase(TestUtilityFunctions))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 80)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print(f"✓ {result.testsRun} tests executed successfully")
        print("✓ ADN-Riemann Encoder validated")
        print("✓ BSD Adélico Connector validated")
        print("✓ Pentagon Logos integration confirmed")
    else:
        print("✗ SOME TESTS FAILED")
        print(f"✗ Failures: {len(result.failures)}")
        print(f"✗ Errors: {len(result.errors)}")
    print("=" * 80)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
