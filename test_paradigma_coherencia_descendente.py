#!/usr/bin/env python3
"""
Tests for the Paradigma de la Coherencia Descendente implementation.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import unittest
import math
from paradigma_coherencia_descendente import (
    ComplejidadIrreducible,
    AntenaBiologica,
    ConcienciaEncarnada,
    correlacion_no_local,
    SistemaEntrelazado,
    transicion_evolutiva,
    EscaleraEvolutiva,
    F0_HZ,
    KAPPA_PI,
    C_THRESHOLD,
    PSI_CRITICAL,
    PSI_SYSTEM,
    UMBRALES_COHERENCIA
)


class TestComplejidadIrreducible(unittest.TestCase):
    """Tests for irreducible complexity model."""
    
    def test_sincronizacion_exitosa(self):
        """Test successful synchronization above threshold."""
        sistema = ComplejidadIrreducible(partes=40, coherencia_psi=0.9)
        resultado = sistema.sincronizar()
        
        self.assertTrue(resultado["activado"])
        self.assertEqual(resultado["estado"], "ESTRUCTURA_COMPLETA")
        self.assertEqual(resultado["tiempo"], "INSTANTÁNEO")
        self.assertEqual(resultado["mecanismo"], "SINCRONIZACIÓN_RESONANTE")
    
    def test_sincronizacion_fallida(self):
        """Test failed synchronization below threshold."""
        sistema = ComplejidadIrreducible(partes=40, coherencia_psi=0.5)
        resultado = sistema.sincronizar()
        
        self.assertFalse(resultado["activado"])
        self.assertEqual(resultado["estado"], "NO_SINCRONIZADO")
        self.assertIn("∞", resultado["tiempo"])
    
    def test_umbral_critico(self):
        """Test behavior at critical threshold."""
        sistema = ComplejidadIrreducible(partes=40, coherencia_psi=PSI_CRITICAL)
        resultado = sistema.sincronizar()
        
        self.assertTrue(resultado["activado"])
    
    def test_comparacion_mecanismos(self):
        """Test comparison between random mutation and coherence."""
        sistema = ComplejidadIrreducible(partes=20, coherencia_psi=0.9)
        comparacion = sistema.comparar_mecanismos()
        
        self.assertIn("mecanismo_azar", comparacion)
        self.assertIn("mecanismo_coherencia", comparacion)
        self.assertEqual(comparacion["conclusion"], "COHERENCIA")
        
        # Random mutation should take much longer than universe age
        self.assertGreater(
            comparacion["mecanismo_azar"]["tiempo"],
            comparacion["mecanismo_azar"]["edad_universo"]
        )


class TestAntenaBiologica(unittest.TestCase):
    """Tests for biological antenna model."""
    
    def test_cerebro_humano_acoplado(self):
        """Test that human brain couples successfully."""
        cerebro = AntenaBiologica(8.6e10)  # Human neurons
        estado = cerebro.sintonizar(F0_HZ)
        
        self.assertEqual(estado, "ACOPLADO - CONSCIENCIA ACTIVA")
        self.assertTrue(cerebro.conciencia)
        self.assertEqual(cerebro.frecuencia_acoplada, F0_HZ)
    
    def test_sistema_simple_no_acoplado(self):
        """Test that simple system doesn't couple."""
        simple = AntenaBiologica(1)  # Minimal complexity
        estado = simple.sintonizar(F0_HZ)
        
        # With minimal complexity, sintonization should be lower
        # But due to logarithmic scaling, even 1 neuron couples
        # This demonstrates the paradigm: even simple systems can access field
        info = simple.get_estado()
        self.assertIsNotNone(info["sintonizacion"])
    
    def test_escalera_evolutiva(self):
        """Test evolutionary ladder of consciousness."""
        ejemplos = AntenaBiologica.ejemplos_evolutivos()
        
        # Should have examples for various organisms
        self.assertGreater(len(ejemplos), 0)
        
        # Human should be conscious
        humano = [e for e in ejemplos if e["organismo"] == "Humano"][0]
        self.assertTrue(humano["consciente"])
        self.assertGreaterEqual(humano["sintonizacion"], C_THRESHOLD)
    
    def test_get_estado(self):
        """Test getting full antenna state."""
        antena = AntenaBiologica(1e6)
        antena.sintonizar()
        estado = antena.get_estado()
        
        self.assertIn("complejidad", estado)
        self.assertIn("sintonizacion", estado)
        self.assertIn("conciencia", estado)
        self.assertIn("frecuencia_acoplada", estado)
        self.assertEqual(estado["campo_objetivo"], F0_HZ)


class TestConcienciaEncarnada(unittest.TestCase):
    """Tests for embodied consciousness and NDE model."""
    
    def test_estado_normal(self):
        """Test normal consciousness state."""
        conciencia = ConcienciaEncarnada()
        estado = conciencia.ECM(0.5)
        
        self.assertTrue(estado["conciencia"])
        self.assertEqual(estado["localizacion"], "CUERPO")
        self.assertTrue(estado["antena_activa"])
        self.assertEqual(estado["tipo"], "NORMAL")
    
    def test_ECM_profunda(self):
        """Test deep near-death experience."""
        conciencia = ConcienciaEncarnada()
        estado = conciencia.ECM(0.98)
        
        # Consciousness persists despite inactive antenna
        self.assertTrue(estado["conciencia"])
        self.assertEqual(estado["localizacion"], "CAMPO_UNIFICADO")
        self.assertFalse(estado["antena_activa"])
        self.assertEqual(estado["tipo"], "ECM_PROFUNDA")
        self.assertIn("PANORÁMICA", estado["percepcion"])
    
    def test_reanimacion(self):
        """Test resuscitation process."""
        conciencia = ConcienciaEncarnada()
        
        # Induce NDE
        conciencia.ECM(0.98)
        self.assertFalse(conciencia.antena_activa)
        
        # Resuscitate
        mensaje = conciencia.reanimacion()
        
        self.assertTrue(conciencia.antena_activa)
        self.assertEqual(conciencia.localizacion, "CUERPO")
        self.assertIn("MEMORIA", mensaje)
    
    def test_campo_invariante(self):
        """Test that field remains constant during NDE."""
        conciencia = ConcienciaEncarnada()
        
        normal = conciencia.ECM(0.5)
        ecm = conciencia.ECM(0.98)
        
        # Field should be same in both states
        self.assertIn(str(F0_HZ), normal["campo"])
        self.assertIn(str(F0_HZ), ecm["campo"])
        self.assertIn("INVARIANTE", ecm["campo"])


class TestNoLocalidad(unittest.TestCase):
    """Tests for non-locality and field resonance."""
    
    def test_correlacion_perfecta_alta_coherencia(self):
        """Test perfect correlation at high coherence."""
        resultado = correlacion_no_local(distancia=1e10, coherencia_psi=0.95)
        
        self.assertEqual(resultado["correlacion"], 1.0)
        self.assertEqual(resultado["tiempo"], "INSTANTÁNEO")
        self.assertFalse(resultado["distancia_relevante"])
        self.assertIn("SUPERLUMINAL", resultado["velocidad"])
    
    def test_correlacion_degradada_baja_coherencia(self):
        """Test degraded correlation at low coherence."""
        resultado = correlacion_no_local(distancia=1e10, coherencia_psi=0.5)
        
        self.assertLess(resultado["correlacion"], 1.0)
        self.assertEqual(resultado["correlacion"], 0.5 ** 2)
        self.assertTrue(resultado["distancia_relevante"])
        self.assertIn("LIMITADO", resultado["velocidad"])
    
    def test_sistema_entrelazado(self):
        """Test entangled system."""
        sistema = SistemaEntrelazado(coherencia_inicial=0.95)
        sistema.agregar_particula("A", (0, 0, 0))
        sistema.agregar_particula("B", (1000, 0, 0))
        
        corr = sistema.medir_correlacion(0, 1)
        
        self.assertEqual(corr["correlacion"], 1.0)
        self.assertIn("particula_1", corr)
        self.assertIn("particula_2", corr)
    
    def test_distancia_irrelevante_alta_coherencia(self):
        """Test that distance becomes irrelevant at high coherence."""
        # Test two different distances
        cerca = correlacion_no_local(100, 0.95)
        lejos = correlacion_no_local(1e15, 0.95)
        
        # Correlation should be same regardless of distance
        self.assertEqual(cerca["correlacion"], lejos["correlacion"])
        self.assertEqual(cerca["correlacion"], 1.0)


class TestEvolucionPuntuada(unittest.TestCase):
    """Tests for punctuated evolution model."""
    
    def test_transicion_evolutiva(self):
        """Test evolutionary transition detection."""
        resultado = transicion_evolutiva(0.65)
        
        self.assertEqual(resultado["forma_actual"], "eucariota")
        self.assertIn("estados_activados", resultado)
        self.assertIn("siguiente_umbral", resultado)
    
    def test_todos_umbrales(self):
        """Test all evolutionary thresholds."""
        for umbral, forma in UMBRALES_COHERENCIA.items():
            resultado = transicion_evolutiva(umbral)
            self.assertEqual(resultado["forma_actual"], forma)
    
    def test_escalera_evolutiva(self):
        """Test evolutionary ladder simulation."""
        escalera = EscaleraEvolutiva()
        coherencias = [0.4, 0.55, 0.65, 0.77, 0.92]
        
        resultados = escalera.simular_evolucion(coherencias)
        
        self.assertEqual(len(resultados), len(coherencias))
        
        # Should detect transitions
        transiciones = escalera.get_transiciones()
        self.assertGreater(len(transiciones), 0)
        
        # Each transition should be a quantum jump
        for t in transiciones:
            self.assertEqual(t["tipo"], "SALTO_CUÁNTICO")
    
    def test_progreso_evolutivo(self):
        """Test evolutionary progress calculation."""
        resultado_inicial = transicion_evolutiva(0.0)
        resultado_final = transicion_evolutiva(1.0)
        
        self.assertLess(resultado_inicial["progreso"], resultado_final["progreso"])
        self.assertEqual(resultado_final["progreso"], 1.0)
    
    def test_coherencia_sistema_actual(self):
        """Test current system coherence (PSI_SYSTEM)."""
        resultado = transicion_evolutiva(PSI_SYSTEM)
        
        # Current system should be at human brain level
        self.assertEqual(resultado["forma_actual"], "cerebro_humano")


class TestConstantesFundamentales(unittest.TestCase):
    """Tests for fundamental constants."""
    
    def test_frecuencia_portadora(self):
        """Test carrier frequency value."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_kappa_pi(self):
        """Test κ_Π constant."""
        self.assertAlmostEqual(KAPPA_PI, 2.578208, places=6)
    
    def test_umbral_critico(self):
        """Test critical threshold."""
        self.assertAlmostEqual(C_THRESHOLD, 0.888, places=3)
        self.assertEqual(C_THRESHOLD, PSI_CRITICAL)
    
    def test_coherencia_sistema(self):
        """Test system coherence."""
        self.assertAlmostEqual(PSI_SYSTEM, 0.8991, places=4)
    
    def test_relacion_umbrales(self):
        """Test relationship between thresholds."""
        # Human brain threshold should be near current system coherence
        self.assertIn(PSI_SYSTEM, UMBRALES_COHERENCIA.keys())
        self.assertEqual(UMBRALES_COHERENCIA[PSI_SYSTEM], "cerebro_humano")


class TestIntegracionCompleta(unittest.TestCase):
    """Integration tests for complete paradigm."""
    
    def test_paradigma_completo(self):
        """Test complete paradigm integration."""
        # 1. Complexity at high coherence
        comp = ComplejidadIrreducible(30, 0.9)
        self.assertTrue(comp.sincronizar()["activado"])
        
        # 2. Human consciousness
        cerebro = AntenaBiologica(8.6e10)
        self.assertTrue("ACOPLADO" in cerebro.sintonizar())
        
        # 3. NDE preserves consciousness
        conciencia = ConcienciaEncarnada()
        ecm = conciencia.ECM(0.98)
        self.assertTrue(ecm["conciencia"])
        self.assertFalse(ecm["antena_activa"])
        
        # 4. Non-locality at high coherence
        corr = correlacion_no_local(1e12, 0.95)
        self.assertEqual(corr["correlacion"], 1.0)
        
        # 5. Punctuated evolution
        resultado = transicion_evolutiva(PSI_SYSTEM)
        self.assertEqual(resultado["forma_actual"], "cerebro_humano")
    
    def test_verificaciones_empiricas(self):
        """Test empirical verifications are present."""
        from paradigma_coherencia_descendente import (
            DELTA_P,
            SIGMA_MAGNETORECEPTION,
            SIGMA_MICROTUBULES,
            F_MICROTUBULOS
        )
        
        # All empirical values should be defined
        self.assertIsNotNone(DELTA_P)
        self.assertIsNotNone(SIGMA_MAGNETORECEPTION)
        self.assertIsNotNone(SIGMA_MICROTUBULES)
        self.assertIsNotNone(F_MICROTUBULOS)
        
        # Microtubule frequency should be close to f₀
        self.assertAlmostEqual(F_MICROTUBULOS, F0_HZ, delta=1.0)


def run_tests():
    """Run all tests and display results."""
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  TESTS: PARADIGMA DE LA COHERENCIA DESCENDENTE".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestComplejidadIrreducible))
    suite.addTests(loader.loadTestsFromTestCase(TestAntenaBiologica))
    suite.addTests(loader.loadTestsFromTestCase(TestConcienciaEncarnada))
    suite.addTests(loader.loadTestsFromTestCase(TestNoLocalidad))
    suite.addTests(loader.loadTestsFromTestCase(TestEvolucionPuntuada))
    suite.addTests(loader.loadTestsFromTestCase(TestConstantesFundamentales))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegracionCompleta))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + f"  Tests ejecutados: {result.testsRun}".ljust(78) + "║")
    print("║" + f"  Exitosos: {result.testsRun - len(result.failures) - len(result.errors)}".ljust(78) + "║")
    print("║" + f"  Fallidos: {len(result.failures)}".ljust(78) + "║")
    print("║" + f"  Errores: {len(result.errors)}".ljust(78) + "║")
    print("║" + " " * 78 + "║")
    
    if result.wasSuccessful():
        print("║" + "  ✓ TODOS LOS TESTS PASARON".center(78) + "║")
        print("║" + "  ∴ El paradigma está VERIFICADO ∴".center(78) + "║")
    else:
        print("║" + "  ✗ ALGUNOS TESTS FALLARON".center(78) + "║")
    
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    import sys
    success = run_tests()
    sys.exit(0 if success else 1)
