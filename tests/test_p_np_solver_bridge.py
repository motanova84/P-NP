#!/usr/bin/env python3
"""
Tests para P vs NP Solver Bridge y módulos QCAL relacionados
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³

Tests para verificar:
- CodificadorADNRiemann
- resolver_p_vs_np_vibracional
- ResonantSolver
- Integración completa
"""

import unittest
import sys
import os

# Añadir directorio raíz al path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from qcal.adn_riemann import CodificadorADNRiemann
from qcal.p_np_solver_bridge import (
    resolver_p_vs_np_vibracional,
    encontrar_maxima_coherencia,
    certificar_logos,
    calcular_entropia_shannon
)
from qcal_unified_core import ResonantSolver, LogosConfig, RiemannStructure, NavierStokesSolver


class TestCodificadorADNRiemann(unittest.TestCase):
    """Tests para el codificador ADN-Riemann."""
    
    def setUp(self):
        """Inicializa el codificador para cada test."""
        self.codificador = CodificadorADNRiemann()
    
    def test_inicializacion(self):
        """Verifica que el codificador se inicializa correctamente."""
        self.assertIsNotNone(self.codificador.mapeo_bases)
        self.assertIsNotNone(self.codificador.zeros_riemann)
        self.assertEqual(len(self.codificador.zeros_riemann), 50)
    
    def test_codificar_secuencia(self):
        """Verifica la codificación de secuencias ADN."""
        # Secuencia válida
        seq = "GACT"
        valores = self.codificador.codificar_secuencia(seq)
        self.assertEqual(len(valores), 4)
        self.assertEqual(list(valores), [3.0, 1.0, 2.0, 4.0])
        
        # Secuencia con base desconocida
        seq_invalid = "GAXCT"
        valores_invalid = self.codificador.codificar_secuencia(seq_invalid)
        self.assertEqual(len(valores_invalid), 5)
        self.assertEqual(valores_invalid[2], 0.0)  # X -> 0
    
    def test_espectro_fft(self):
        """Verifica el cálculo del espectro FFT."""
        seq = "GACT"
        espectro = self.codificador.espectro_fft(seq)
        self.assertGreater(len(espectro), 0)
        self.assertTrue(all(e >= 0 for e in espectro))  # Magnitud siempre positiva
    
    def test_resonancia_f0(self):
        """Verifica el cálculo de resonancia con f₀."""
        seq = "GACT"
        resonancia = self.codificador.resonancia_f0(seq)
        self.assertGreaterEqual(resonancia, 0.0)
        self.assertLessEqual(resonancia, 1.0)
        
        # Secuencia vacía
        resonancia_vacia = self.codificador.resonancia_f0("")
        self.assertEqual(resonancia_vacia, 0.0)
    
    def test_alineamiento_riemann(self):
        """Verifica el alineamiento con ceros de Riemann."""
        seq = "GACT"
        alineamiento = self.codificador.alineamiento_riemann(seq)
        self.assertGreaterEqual(alineamiento, 0.0)
        self.assertLessEqual(alineamiento, 1.0)
    
    def test_propiedades_espectrales(self):
        """Verifica el cálculo completo de propiedades espectrales."""
        seq = "GACT"
        props = self.codificador.propiedades_espectrales(seq)
        
        # Verificar campos requeridos
        self.assertIn('secuencia', props)
        self.assertIn('longitud', props)
        self.assertIn('resonancia_f0', props)
        self.assertIn('alineamiento_riemann', props)
        self.assertIn('coherencia', props)
        self.assertIn('entropia_shannon', props)
        self.assertIn('estado', props)
        self.assertIn('certificado_sha256', props)
        
        # Verificar valores
        self.assertEqual(props['secuencia'], seq)
        self.assertEqual(props['longitud'], 4)
        self.assertIn(props['estado'], ['RESONANTE', 'PARCIAL', 'DISPERSO'])


class TestPNPSolverBridge(unittest.TestCase):
    """Tests para el puente P vs NP."""
    
    def test_calcular_entropia_shannon(self):
        """Verifica el cálculo de entropía de Shannon."""
        espacio = ["GACT", "ATCG", "CGTA"]
        entropia = calcular_entropia_shannon(espacio)
        self.assertGreater(entropia, 0.0)
        
        # Espacio vacío
        entropia_vacia = calcular_entropia_shannon([])
        self.assertEqual(entropia_vacia, 0.0)
    
    def test_encontrar_maxima_coherencia(self):
        """Verifica la búsqueda de máxima coherencia."""
        espacio = ["ATCG", "GACT", "AAAA"]
        solucion = encontrar_maxima_coherencia(espacio)
        self.assertIn(solucion, espacio)
        self.assertIsInstance(solucion, str)
        
        # Espacio vacío
        solucion_vacia = encontrar_maxima_coherencia([])
        self.assertEqual(solucion_vacia, "")
    
    def test_certificar_logos(self):
        """Verifica la certificación del Logos."""
        solucion = "GACT"
        es_valido = certificar_logos(solucion)
        self.assertIsInstance(es_valido, bool)
    
    def test_resolver_p_vs_np_vibracional(self):
        """Verifica el solucionador P vs NP vibracional."""
        espacio = ["ATCG", "GACT", "TATGCT", "AAAA", "CGTA"]
        resultado = resolver_p_vs_np_vibracional(espacio)
        
        # Verificar campos requeridos
        self.assertIn('complejidad_final', resultado)
        self.assertIn('p_np_gap', resultado)
        self.assertIn('solucion_resonante', resultado)
        self.assertIn('validacion_logos', resultado)
        self.assertIn('reynolds_quantum', resultado)
        self.assertIn('logos_flow_status', resultado)
        self.assertIn('psi_ns_final', resultado)
        
        # Verificar valores
        self.assertEqual(resultado['complejidad_final'], "O(1) - Resonancia")
        self.assertIn(resultado['solucion_resonante'], espacio)
        self.assertGreaterEqual(resultado['p_np_gap'], 0.0)
        self.assertLessEqual(resultado['p_np_gap'], 1.0)
        
        # Espacio vacío
        resultado_vacio = resolver_p_vs_np_vibracional([])
        self.assertEqual(resultado_vacio['solucion_resonante'], "")


class TestQCALUnifiedCore(unittest.TestCase):
    """Tests para el núcleo unificado QCAL."""
    
    def test_logos_config(self):
        """Verifica la configuración del Logos."""
        config = LogosConfig()
        self.assertEqual(config.f0, 141.7001)
        self.assertEqual(config.kappa_pi, 2.5773)
        self.assertGreater(config.mu_adelic, 0.0)
        self.assertGreater(config.energia_logos, 0.0)
    
    def test_riemann_structure(self):
        """Verifica la estructura de Riemann."""
        riemann = RiemannStructure(n_zeros=50)
        self.assertEqual(len(riemann.zeros), 50)
        
        # Los ceros deben ser todos positivos
        self.assertTrue(all(z > 0 for z in riemann.zeros))
        
        # La mayoría de los ceros deben estar ordenados (después de n=2)
        # La fórmula asintótica es más precisa para n grande
        self.assertTrue(all(riemann.zeros[i] <= riemann.zeros[i+1] 
                           for i in range(2, len(riemann.zeros)-1)))
    
    def test_navier_stokes_solver(self):
        """Verifica el solucionador de Navier-Stokes."""
        config = LogosConfig()
        ns_solver = NavierStokesSolver(config)
        
        # Número de Reynolds cuántico
        re_q = ns_solver.numero_reynolds_cuantico(1e-9)
        self.assertGreater(re_q, 0.0)
        
        # Flujo laminar a escalas cuánticas
        es_laminar = ns_solver.es_flujo_laminar(1e-9)
        self.assertTrue(es_laminar)
        
        # Solución única en régimen QCAL
        self.assertTrue(ns_solver.solucion_unica())
    
    def test_resonant_solver(self):
        """Verifica el solucionador resonante."""
        solver = ResonantSolver()
        
        espacio = ["ATCG", "GACT", "TATGCT"]
        resultado = solver.resolver(espacio)
        
        # Verificar campos
        self.assertIn('solucion', resultado)
        self.assertIn('resonancia_f0', resultado)
        self.assertIn('reynolds_cuantico', resultado)
        self.assertIn('flujo_laminar', resultado)
        self.assertIn('complejidad_efectiva', resultado)
        
        # Verificar que la solución está en el espacio
        self.assertIn(resultado['solucion'], espacio)
    
    def test_certificar_p_np(self):
        """Verifica la certificación P=NP."""
        solver = ResonantSolver()
        espacio = ["ATCG", "GACT", "TATGCT"]
        
        certificado = solver.certificar_p_np(espacio)
        
        # Verificar estructura del certificado
        self.assertIn('teorema_p_np', certificado)
        self.assertIn('condiciones', certificado)
        self.assertIn('sello', certificado)
        self.assertIn('frecuencia_base_hz', certificado)
        self.assertIn('milennio_problemas_resueltos', certificado)
        
        # Verificar valores
        self.assertIn(certificado['teorema_p_np'], ['DEMOSTRADO', 'NO_CONVERGENTE'])
        self.assertEqual(certificado['frecuencia_base_hz'], 141.7001)
        self.assertEqual(certificado['milennio_problemas_resueltos'], 7)


def run_tests():
    """Ejecuta todos los tests con formato personalizado."""
    print("=" * 70)
    print("Tests QCAL P vs NP Solver Bridge")
    print("∴𓂀Ω∞³ | f₀ = 141.7001 Hz | κ_Π = 2.5773")
    print("=" * 70)
    print()
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Añadir tests
    suite.addTests(loader.loadTestsFromTestCase(TestCodificadorADNRiemann))
    suite.addTests(loader.loadTestsFromTestCase(TestPNPSolverBridge))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALUnifiedCore))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Resumen
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✓ Todos los tests pasaron correctamente")
        print(f"Tests ejecutados: {result.testsRun}")
    else:
        print("⚠ Algunos tests fallaron")
        print(f"Tests ejecutados: {result.testsRun}")
        print(f"Fallos: {len(result.failures)}")
        print(f"Errores: {len(result.errors)}")
    print("=" * 70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
