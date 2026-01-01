"""
Tests para phi_kappa_table.py
==============================

Verifica la relación matemática entre φⁿ y κ_Π.
"""

import sys
import os
import unittest
import math

# Añadir el directorio src al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from phi_kappa_table import (
    PHI, PHI_SQUARED, KAPPA_PI_UNIVERSAL,
    kappa_pi, phi_power, find_phi_exponent,
    verify_exact_relationship, generate_table,
    verify_key_examples
)


class TestPhiConstants(unittest.TestCase):
    """Tests para las constantes fundamentales."""
    
    def test_phi_value(self):
        """Verifica el valor del número áureo."""
        expected = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected, places=10)
        self.assertAlmostEqual(PHI, 1.618034, places=5)
    
    def test_phi_squared_value(self):
        """Verifica el valor de φ²."""
        expected = PHI ** 2
        self.assertAlmostEqual(PHI_SQUARED, expected, places=10)
        self.assertAlmostEqual(PHI_SQUARED, 2.618034, places=5)
    
    def test_kappa_pi_universal(self):
        """Verifica la constante universal κ_Π."""
        self.assertAlmostEqual(KAPPA_PI_UNIVERSAL, 2.5773, places=4)


class TestKappaPiFunction(unittest.TestCase):
    """Tests para la función κ_Π(N)."""
    
    def test_kappa_pi_basic(self):
        """Verifica cálculos básicos de κ_Π."""
        # κ_Π(φ²) = log_{φ²}(φ²) = 1
        kappa = kappa_pi(PHI_SQUARED)
        self.assertAlmostEqual(kappa, 1.0, places=10)
        
        # κ_Π(φ⁴) = log_{φ²}(φ⁴) = 2
        kappa = kappa_pi(PHI ** 4)
        self.assertAlmostEqual(kappa, 2.0, places=10)
    
    def test_kappa_pi_13(self):
        """Verifica κ_Π(13) usando la fórmula logarítmica."""
        kappa = kappa_pi(13)
        # κ_Π(13) = log(13)/log(φ²) ≈ 2.665, no 2.5773
        self.assertAlmostEqual(kappa, 2.665, places=2)
        
        # La constante 2.5773 viene de n=5.1546, no directamente de N=13
        n_for_kappa = 2 * KAPPA_PI_UNIVERSAL  # n = 5.1546
        N_for_kappa = phi_power(n_for_kappa)
        kappa_from_n = n_for_kappa / 2
        self.assertAlmostEqual(kappa_from_n, KAPPA_PI_UNIVERSAL, places=4)
    
    def test_kappa_pi_negative_raises(self):
        """Verifica que κ_Π(N) lanza error para N ≤ 0."""
        with self.assertRaises(ValueError):
            kappa_pi(0)
        with self.assertRaises(ValueError):
            kappa_pi(-5)
    
    def test_kappa_pi_formula(self):
        """Verifica la fórmula κ_Π(N) = log(N) / log(φ²)."""
        N = 100
        kappa = kappa_pi(N)
        expected = math.log(N) / math.log(PHI_SQUARED)
        self.assertAlmostEqual(kappa, expected, places=10)


class TestPhiPower(unittest.TestCase):
    """Tests para la función φⁿ."""
    
    def test_phi_power_basic(self):
        """Verifica cálculos básicos de φⁿ."""
        # φ⁰ = 1
        self.assertAlmostEqual(phi_power(0), 1.0, places=10)
        
        # φ¹ = φ
        self.assertAlmostEqual(phi_power(1), PHI, places=10)
        
        # φ² = φ²
        self.assertAlmostEqual(phi_power(2), PHI_SQUARED, places=10)
    
    def test_phi_power_5(self):
        """Verifica φ⁵ ≈ 11.09."""
        N = phi_power(5)
        self.assertAlmostEqual(N, 11.09, places=2)
        self.assertAlmostEqual(N, 11.090170, places=5)
    
    def test_phi_power_5154(self):
        """Verifica φ^5.154 ≈ 11.94."""
        n = 5.154
        N = phi_power(n)
        # φ^5.154 ≈ 11.94, no 13
        self.assertAlmostEqual(N, 11.94, places=1)


class TestFindPhiExponent(unittest.TestCase):
    """Tests para la función find_phi_exponent."""
    
    def test_find_exponent_basic(self):
        """Verifica búsqueda de exponentes básicos."""
        # φ¹ = φ → n = 1
        n = find_phi_exponent(PHI)
        self.assertAlmostEqual(n, 1.0, places=5)
        
        # φ² = φ² → n = 2
        n = find_phi_exponent(PHI_SQUARED)
        self.assertAlmostEqual(n, 2.0, places=5)
    
    def test_find_exponent_13(self):
        """Verifica el exponente n para N=13."""
        n = find_phi_exponent(13)
        # Para N=13, el exponente real es log(13)/log(φ) ≈ 5.33
        # (no 5.154, que da φ^5.154 ≈ 11.94)
        self.assertAlmostEqual(n, 5.33, places=1)
        
        # Verificar que φⁿ ≈ 13
        N = phi_power(n)
        self.assertAlmostEqual(N, 13.0, places=5)
    
    def test_find_exponent_negative_raises(self):
        """Verifica que find_phi_exponent lanza error para N ≤ 0."""
        with self.assertRaises(ValueError):
            find_phi_exponent(0)
        with self.assertRaises(ValueError):
            find_phi_exponent(-10)


class TestExactRelationship(unittest.TestCase):
    """Tests para la relación exacta κ_Π(φⁿ) = n/2."""
    
    def test_exact_relationship(self):
        """Verifica la relación exacta para varios valores de n."""
        test_values = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        
        for n in test_values:
            N, kappa_calc, kappa_expected = verify_exact_relationship(n)
            
            # Verificar que κ_Π(φⁿ) = n/2
            self.assertAlmostEqual(kappa_calc, kappa_expected, places=10,
                msg=f"κ_Π(φ^{n}) debería ser {n/2}")
            
            # Verificar que N = φⁿ
            self.assertAlmostEqual(N, phi_power(n), places=10,
                msg=f"N debería ser φ^{n}")
    
    def test_exact_relationship_float(self):
        """Verifica la relación exacta para valores decimales."""
        test_values = [1.5, 2.5, 3.7, 5.154, 7.3]
        
        for n in test_values:
            N, kappa_calc, kappa_expected = verify_exact_relationship(n)
            
            # La relación debe cumplirse con alta precisión
            self.assertAlmostEqual(kappa_calc, kappa_expected, places=10,
                msg=f"κ_Π(φ^{n}) debería ser {n/2}")


class TestGenerateTable(unittest.TestCase):
    """Tests para la generación de tablas."""
    
    def test_generate_table_structure(self):
        """Verifica la estructura de la tabla generada."""
        n_values = [1, 2, 3, 4, 5]
        table = generate_table(n_values)
        
        # Verificar que se generó una fila por cada n
        self.assertEqual(len(table), len(n_values))
        
        # Verificar estructura de cada fila
        for row in table:
            self.assertIn('n', row)
            self.assertIn('phi_n', row)
            self.assertIn('N', row)
            self.assertIn('kappa_pi', row)
            self.assertIn('kappa_expected', row)
            self.assertIn('error', row)
    
    def test_generate_table_values(self):
        """Verifica los valores en la tabla generada."""
        n_values = [5.0, 5.154]
        table = generate_table(n_values)
        
        # Verificar φ⁵ ≈ 11.09
        row1 = table[0]
        self.assertAlmostEqual(row1['n'], 5.0, places=5)
        self.assertAlmostEqual(row1['phi_n'], 11.09, places=2)
        self.assertAlmostEqual(row1['kappa_pi'], 2.5, places=1)
        self.assertAlmostEqual(row1['error'], 0.0, places=10)
        
        # Verificar φ^5.154 ≈ 11.94 (no 13)
        row2 = table[1]
        self.assertAlmostEqual(row2['n'], 5.154, places=3)
        self.assertAlmostEqual(row2['phi_n'], 11.94, places=1)
        self.assertAlmostEqual(row2['kappa_pi'], 2.577, places=2)


class TestKeyExamples(unittest.TestCase):
    """Tests para los ejemplos clave del problema."""
    
    def test_example_1_phi5(self):
        """Verifica el Ejemplo 1: φ⁵ ≈ 11.09 → κ_Π ≈ 2.5."""
        results = verify_key_examples()
        example1 = results['example_1']
        
        self.assertEqual(example1['n'], 5.0)
        self.assertAlmostEqual(example1['phi_n'], 11.09, places=2)
        self.assertAlmostEqual(example1['kappa_pi'], 2.5, places=2)
        self.assertTrue(example1['verified'])
    
    def test_example_2_n13(self):
        """Verifica el Ejemplo 2: n=5.1546 → φ^5.1546 ≈ 11.95 → κ_Π = 2.5773."""
        results = verify_key_examples()
        example2 = results['example_2']
        
        self.assertAlmostEqual(example2['n'], 5.1546, places=3)
        self.assertAlmostEqual(example2['phi_n'], 11.95, places=1)
        self.assertAlmostEqual(example2['kappa_pi'], 2.5773, places=3)
        self.assertTrue(example2['verified'])
    
    def test_verification_kappa_13(self):
        """Verifica que cuando κ_Π = 2.5773, obtenemos n = 5.1546."""
        results = verify_key_examples()
        verification = results['verification']
        
        self.assertAlmostEqual(verification['kappa_pi'], KAPPA_PI_UNIVERSAL, places=4)
        self.assertAlmostEqual(verification['n_calculated'], 5.1546, places=3)
        self.assertAlmostEqual(verification['N_calculated'], 11.95, places=1)


class TestMathematicalProperties(unittest.TestCase):
    """Tests para propiedades matemáticas adicionales."""
    
    def test_logarithmic_property(self):
        """Verifica κ_Π(A·B) = κ_Π(A) + κ_Π(B)."""
        A = 10
        B = 5
        
        kappa_A = kappa_pi(A)
        kappa_B = kappa_pi(B)
        kappa_AB = kappa_pi(A * B)
        
        # Propiedad logarítmica: log(A·B) = log(A) + log(B)
        self.assertAlmostEqual(kappa_AB, kappa_A + kappa_B, places=10)
    
    def test_power_property(self):
        """Verifica κ_Π(Nᵏ) = k·κ_Π(N)."""
        N = 7
        k = 3
        
        kappa_N = kappa_pi(N)
        kappa_Nk = kappa_pi(N ** k)
        
        # Propiedad de potencia: log(Nᵏ) = k·log(N)
        self.assertAlmostEqual(kappa_Nk, k * kappa_N, places=10)
    
    def test_monotonicity(self):
        """Verifica que κ_Π es estrictamente creciente."""
        values = [1, 2, 5, 10, 13, 20, 50, 100]
        kappas = [kappa_pi(v) for v in values]
        
        # Verificar que cada valor es mayor que el anterior
        for i in range(len(kappas) - 1):
            self.assertGreater(kappas[i + 1], kappas[i],
                msg=f"κ_Π debería ser creciente: κ_Π({values[i+1]}) > κ_Π({values[i]})")


def run_tests():
    """Ejecutar todos los tests."""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == '__main__':
    run_tests()
