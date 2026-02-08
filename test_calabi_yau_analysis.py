#!/usr/bin/env python3
"""
Tests para calabi_yau_analysis.py
"""

import math
import numpy as np
from calabi_yau_analysis import comprehensive_analysis, real_cy_sample


def test_comprehensive_analysis():
    """Test básico de la función comprehensive_analysis."""
    # Ejecutar análisis con datos de prueba
    kappas, N_values, stats = comprehensive_analysis(real_cy_sample)
    
    # Verificar que tenemos resultados
    assert len(kappas) == len(real_cy_sample), "Número de kappas debe coincidir con datos"
    assert len(N_values) == len(real_cy_sample), "Número de N_values debe coincidir con datos"
    
    # Verificar que kappas se calculan correctamente
    for i, (h11, h21) in enumerate(real_cy_sample):
        N = h11 + h21
        expected_kappa = math.log2(N)
        assert abs(kappas[i] - expected_kappa) < 1e-10, f"Kappa {i} mal calculado"
        assert N_values[i] == N, f"N_value {i} mal calculado"
    
    # Verificar estadísticas básicas
    assert stats['n_samples'] == len(real_cy_sample), "n_samples incorrecto"
    assert abs(stats['kappa_mean'] - np.mean(kappas)) < 1e-10, "kappa_mean incorrecto"
    assert abs(stats['kappa_median'] - np.median(kappas)) < 1e-10, "kappa_median incorrecto"
    assert stats['N_min'] == min(N_values), "N_min incorrecto"
    assert stats['N_max'] == max(N_values), "N_max incorrecto"
    
    # Verificar log2(13)
    assert abs(stats['log2_13_value'] - math.log2(13)) < 1e-10, "log2_13_value incorrecto"
    
    # Verificar que shapiro_p existe
    assert 'shapiro_p' in stats, "shapiro_p debe estar en stats"
    assert 0 <= stats['shapiro_p'] <= 1, "shapiro_p debe estar entre 0 y 1"
    
    print("✅ Todos los tests pasaron correctamente")


def test_log2_13_calculation():
    """Verificar que log₂(13) se calcula correctamente."""
    expected = math.log2(13)
    # Verificar que esté en el rango esperado (≈ 3.7004)
    assert 3.70 < expected < 3.71, "log2(13) debe estar cerca de 3.7004"
    print(f"✅ log₂(13) = {expected:.10f}")


def test_n13_count():
    """Verificar que se cuentan correctamente las variedades con N=13."""
    kappas, N_values, stats = comprehensive_analysis(real_cy_sample)
    
    # Contar manualmente N=13
    manual_count = sum(1 for h11, h21 in real_cy_sample if h11 + h21 == 13)
    
    assert stats['n13_count'] == manual_count, f"n13_count debe ser {manual_count}"
    assert abs(stats['n13_fraction'] - manual_count / len(real_cy_sample)) < 1e-10
    
    print(f"✅ N=13 aparece {manual_count} veces de {len(real_cy_sample)} muestras")


def test_sample_data_validity():
    """Verificar que los datos de muestra sean válidos."""
    for i, (h11, h21) in enumerate(real_cy_sample):
        assert h11 >= 0, f"h11 debe ser no negativo en muestra {i}"
        assert h21 >= 0, f"h21 debe ser no negativo en muestra {i}"
        assert h11 + h21 > 0, f"h11 + h21 debe ser positivo en muestra {i}"
    
    print(f"✅ Datos de muestra válidos: {len(real_cy_sample)} variedades")


def test_error_handling():
    """Verificar que se manejan correctamente los errores."""
    # Test con datos vacíos
    try:
        comprehensive_analysis([])
        assert False, "Debería lanzar ValueError con datos vacíos"
    except ValueError as e:
        assert "vacío" in str(e).lower()
        print("✅ Error correcto con datos vacíos")
    
    # Test con N = 0
    try:
        comprehensive_analysis([(0, 0)])
        assert False, "Debería lanzar ValueError con N = 0"
    except ValueError as e:
        assert "positivo" in str(e).lower()
        print("✅ Error correcto con N = 0")
    
    # Test con valores negativos
    try:
        comprehensive_analysis([(-1, 5)])
        assert False, "Debería lanzar ValueError con valores negativos"
    except ValueError as e:
        assert "negativo" in str(e).lower()
        print("✅ Error correcto con valores negativos")


if __name__ == "__main__":
    print("="*70)
    print("TESTS DE CALABI-YAU ANALYSIS".center(70))
    print("="*70)
    print()
    
    test_sample_data_validity()
    test_error_handling()
    test_log2_13_calculation()
    test_n13_count()
    test_comprehensive_analysis()
    
    print()
    print("="*70)
    print("TODOS LOS TESTS COMPLETADOS EXITOSAMENTE".center(70))
    print("="*70)
