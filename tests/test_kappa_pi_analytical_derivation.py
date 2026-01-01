#!/usr/bin/env python3
"""
Tests para la Derivación Analítica de Propiedades Matemáticas de κ_Π(N)
========================================================================

Valida todas las propiedades matemáticas derivadas en las secciones I-VII.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import math
import numpy as np
from src.kappa_pi_analytical_derivation import KappaPiAnalyticalDerivation


@pytest.fixture
def analyzer():
    """Fixture para crear una instancia del analizador."""
    return KappaPiAnalyticalDerivation()


class TestSectionI_FormalDefinition:
    """Tests para Sección I: Definición Formal"""
    
    def test_phi_value(self, analyzer):
        """Verificar valor del número áureo φ."""
        expected_phi = (1 + math.sqrt(5)) / 2
        assert abs(analyzer.phi - expected_phi) < 1e-15
        assert abs(analyzer.phi - 1.618033988749895) < 1e-10
    
    def test_phi_squared_value(self, analyzer):
        """Verificar valor de φ²."""
        # φ² = φ + 1 (propiedad del número áureo)
        assert abs(analyzer.phi_squared - (analyzer.phi + 1)) < 1e-15
        
        # φ² = (3 + √5) / 2
        expected_phi2 = (3 + math.sqrt(5)) / 2
        assert abs(analyzer.phi_squared - expected_phi2) < 1e-15
        assert abs(analyzer.phi_squared - 2.6180339887) < 1e-9
    
    def test_ln_values(self, analyzer):
        """Verificar valores de logaritmos naturales."""
        assert abs(analyzer.ln_phi - math.log(analyzer.phi)) < 1e-15
        assert abs(analyzer.ln_phi_squared - math.log(analyzer.phi_squared)) < 1e-15
        assert abs(analyzer.ln_phi_squared - 2 * analyzer.ln_phi) < 1e-15
    
    def test_kappa_pi_definition(self, analyzer):
        """Verificar que κ_Π cumple con la definición."""
        N = 10
        kappa = analyzer.kappa_pi(N)
        expected = math.log(N) / analyzer.ln_phi_squared
        assert abs(kappa - expected) < 1e-15
    
    def test_kappa_pi_positive_domain(self, analyzer):
        """Verificar que κ_Π requiere N > 0."""
        with pytest.raises(ValueError):
            analyzer.kappa_pi(0)
        with pytest.raises(ValueError):
            analyzer.kappa_pi(-5)
    
    def test_formal_definition_dict(self, analyzer):
        """Verificar estructura del diccionario de definición formal."""
        formal_def = analyzer.formal_definition()
        
        assert 'definition' in formal_def
        assert 'phi' in formal_def
        assert 'phi_squared' in formal_def
        assert 'ln_phi' in formal_def
        assert 'ln_phi_squared' in formal_def
        assert 'domain' in formal_def
        assert formal_def['strictly_increasing'] is True


class TestSectionII_BasicProperties:
    """Tests para Sección II: Propiedades Básicas"""
    
    def test_strictly_increasing(self, analyzer):
        """Verificar que κ_Π(N) es estrictamente creciente."""
        N_values = [1, 2, 3, 5, 10, 13, 20, 50, 100]
        kappa_values = [analyzer.kappa_pi(N) for N in N_values]
        
        # Verificar monotonía estricta
        for i in range(len(kappa_values) - 1):
            assert kappa_values[i] < kappa_values[i+1]
    
    def test_power_property(self, analyzer):
        """Verificar que κ_Π((φ²)^k) = k."""
        for k in [0.5, 1, 1.5, 2, 2.5, 3, 4, 5]:
            N = analyzer.phi_squared ** k
            kappa = analyzer.kappa_pi(N)
            assert abs(kappa - k) < 1e-10, f"Para k={k}, esperado {k}, obtenido {kappa}"
    
    def test_derivative_formula(self, analyzer):
        """Verificar fórmula de la derivada numéricamente."""
        test_points = [1, 5, 10, 13, 20, 50]
        h = 1e-8
        
        for N in test_points:
            # Derivada numérica (diferencia central)
            numerical = (analyzer.kappa_pi(N + h) - analyzer.kappa_pi(N - h)) / (2 * h)
            
            # Derivada analítica: 1 / (N · ln(φ²))
            analytical = 1 / (N * analyzer.ln_phi_squared)
            
            relative_error = abs(numerical - analytical) / abs(analytical)
            assert relative_error < 1e-6, f"Error en N={N}: {relative_error}"
    
    def test_derivative_decreasing(self, analyzer):
        """Verificar que la derivada decrece con N."""
        N_values = [1, 5, 10, 20, 50, 100]
        derivatives = [1 / (N * analyzer.ln_phi_squared) for N in N_values]
        
        # La derivada debe decrecer
        for i in range(len(derivatives) - 1):
            assert derivatives[i] > derivatives[i+1]
    
    def test_basic_properties_dict(self, analyzer):
        """Verificar estructura del análisis de propiedades básicas."""
        props = analyzer.basic_properties()
        
        assert props['strictly_increasing'] is True
        assert props['power_property']['holds'] is True
        assert props['derivative']['matches'] is True
        assert abs(props['derivative']['error']) < 1e-6


class TestSectionIII_InverseFunction:
    """Tests para Sección III: Inversa Formal"""
    
    def test_inverse_formula(self, analyzer):
        """Verificar que la inversa cumple N = (φ²)^x."""
        x_values = [0, 0.5, 1, 1.5, 2, 2.5, 3]
        
        for x in x_values:
            N = analyzer.inverse_function(x)
            expected = analyzer.phi_squared ** x
            assert abs(N - expected) < 1e-15
    
    def test_inverse_composition(self, analyzer):
        """Verificar que κ_Π(N) y su inversa se cancelan."""
        x_values = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5]
        
        for x in x_values:
            N = analyzer.inverse_function(x)
            x_recovered = analyzer.kappa_pi(N)
            assert abs(x_recovered - x) < 1e-10
    
    def test_inverse_forward_composition(self, analyzer):
        """Verificar composición en sentido inverso."""
        N_values = [1, 5, 10, 13, 20, 50]
        
        for N in N_values:
            x = analyzer.kappa_pi(N)
            N_recovered = analyzer.inverse_function(x)
            assert abs(N_recovered - N) < 1e-10
    
    def test_inverse_analysis_dict(self, analyzer):
        """Verificar estructura del análisis de la inversa."""
        inv_analysis = analyzer.inverse_analysis()
        
        assert 'formula' in inv_analysis
        assert inv_analysis['formula'] == 'N = (φ²)^x'
        assert inv_analysis['all_correct'] is True
        assert inv_analysis['base'] == analyzer.phi_squared


class TestSectionIV_BaseComparisons:
    """Tests para Sección IV: Diferencias con Otras Bases"""
    
    def test_base_values(self, analyzer):
        """Verificar valores de ln para diferentes bases."""
        assert abs(analyzer.ln_phi_squared - 0.962423650119206) < 1e-10
        assert abs(analyzer.ln_2 - 0.6931471805599453) < 1e-10
        assert abs(analyzer.ln_e - 1.0) < 1e-15
    
    def test_inequality_ln_phi2_gt_ln2(self, analyzer):
        """Verificar que ln(φ²) > ln(2)."""
        assert analyzer.ln_phi_squared > analyzer.ln_2
    
    def test_log_ordering_for_N_gt_1(self, analyzer):
        """Verificar que log_2(N) > log_φ²(N) > log_e(N) para N > 1."""
        N_values = [2, 5, 10, 13, 20, 100, 1000]
        
        for N in N_values:
            log_phi2 = analyzer.kappa_pi(N)
            log_e = math.log(N)
            log_2 = math.log(N) / analyzer.ln_2
            
            # Orden correcto: log_2(N) > log_φ²(N) > log_e(N)
            assert log_2 > log_phi2, f"Falla en N={N}: log_2({N}) no > log_φ²({N})"
            assert log_phi2 > log_e, f"Falla en N={N}: log_φ²({N}) no > log_e({N})"
    
    def test_compare_with_bases_dict(self, analyzer):
        """Verificar estructura de comparación de bases."""
        comp = analyzer.compare_with_bases(13)
        
        assert comp['N'] == 13
        assert 'log_phi2' in comp
        assert 'log_e' in comp
        assert 'log_2' in comp
        assert 'comparison' in comp
    
    def test_base_comparison_analysis(self, analyzer):
        """Verificar análisis completo de comparación de bases."""
        analysis = analyzer.base_comparison_analysis()
        
        assert 'bases' in analysis
        assert 'ln_values_approx' in analysis
        assert 'inequality' in analysis
        assert 'implication' in analysis


class TestSectionV_ResidueStructure:
    """Tests para Sección V: Estructura de Residuos"""
    
    def test_phi2_is_irrational(self, analyzer):
        """Verificar que φ² es irracional (implícito en el análisis)."""
        # φ² = (3 + √5) / 2, que es irracional porque √5 es irracional
        # No podemos probar directamente, pero verificamos consistencia
        assert analyzer.phi_squared > 0
        assert not analyzer.phi_squared.is_integer()
    
    def test_integer_kappa_for_powers(self, analyzer):
        """Verificar que κ_Π es entero para potencias exactas de φ²."""
        for k in range(1, 6):
            N = analyzer.phi_squared ** k
            kappa = analyzer.kappa_pi(N)
            assert abs(kappa - round(kappa)) < 1e-10
    
    def test_non_integer_kappa_for_most_N(self, analyzer):
        """Verificar que κ_Π no es entero para la mayoría de N."""
        # N que no son potencias de φ²
        N_values = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        
        for N in N_values:
            kappa = analyzer.kappa_pi(N)
            # No debe ser entero (margen para error numérico)
            assert abs(kappa - round(kappa)) > 1e-6
    
    def test_residue_structure_dict(self, analyzer):
        """Verificar estructura del análisis de residuos."""
        residue = analyzer.residue_structure(13)
        
        assert residue['N'] == 13
        assert 'kappa_N' in residue
        assert 'is_integer' in residue
        assert 'is_rational' in residue
        assert residue['phi2_irrational'] is True
        assert 'decimal_expansion' in residue
    
    def test_residue_analysis_multiple(self, analyzer):
        """Verificar análisis de residuos para múltiples valores."""
        analysis = analyzer.residue_analysis([2, 5, 10, 13, 20])
        
        assert 'analyses' in analysis
        assert len(analysis['analyses']) == 5
        assert 'summary' in analysis
        assert analysis['summary']['phi2_irrational'] is True


class TestSectionVI_SpecialCaseN13:
    """Tests para Sección VI: Especialidad de κ_Π(13)"""
    
    def test_kappa_13_value(self, analyzer):
        """Verificar valor de κ_Π(13)."""
        kappa_13 = analyzer.kappa_pi(13)
        
        # Cálculo manual
        expected = math.log(13) / analyzer.ln_phi_squared
        assert abs(kappa_13 - expected) < 1e-15
        
        # Valor aproximado
        assert abs(kappa_13 - 2.6651) < 0.001
    
    def test_kappa_13_not_equal_2_5773(self, analyzer):
        """Verificar que κ_Π(13) ≠ 2.5773 exactamente."""
        kappa_13 = analyzer.kappa_pi(13)
        assert abs(kappa_13 - 2.5773) > 0.05
    
    def test_N_star_for_2_5773(self, analyzer):
        """Verificar N* tal que κ_Π(N*) = 2.5773."""
        target = 2.5773
        N_star = analyzer.inverse_function(target)
        
        # Verificar que κ_Π(N*) = 2.5773
        kappa_N_star = analyzer.kappa_pi(N_star)
        assert abs(kappa_N_star - target) < 1e-10
        
        # N* debe estar cerca de 12-13
        assert 11 < N_star < 14
    
    def test_special_case_dict(self, analyzer):
        """Verificar estructura del análisis especial de N=13."""
        special = analyzer.special_case_N13()
        
        assert special['N'] == 13
        assert 'kappa_13' in special
        assert special['not_equal_to_2_5773'] is True
        assert 'analysis' in special
        assert special['analysis']['no_ad_hoc_adjustments'] is True
        assert 'geometric_significance' in special


class TestSectionVII_AnalyticalConclusion:
    """Tests para Sección VII: Conclusión Analítica"""
    
    def test_conclusion_dict_structure(self, analyzer):
        """Verificar estructura del diccionario de conclusiones."""
        conclusion = analyzer.analytical_conclusion()
        
        assert 'function' in conclusion
        assert 'properties' in conclusion
        assert 'key_results' in conclusion
        assert 'geometric_meaning' in conclusion
        assert 'special_values' in conclusion
        assert 'complete_analysis' in conclusion
    
    def test_special_values_in_conclusion(self, analyzer):
        """Verificar valores especiales en la conclusión."""
        conclusion = analyzer.analytical_conclusion()
        special_vals = conclusion['special_values']
        
        # κ_Π(φ²) = 1
        assert abs(special_vals['N=(φ²)'] - 1.0) < 1e-10
        
        # κ_Π((φ²)²) = 2
        assert abs(special_vals['N=(φ²)²'] - 2.0) < 1e-10
        
        # κ_Π((φ²)³) = 3
        assert abs(special_vals['N=(φ²)³'] - 3.0) < 1e-10
    
    def test_properties_verification(self, analyzer):
        """Verificar que todas las propiedades declaradas son correctas."""
        conclusion = analyzer.analytical_conclusion()
        props = conclusion['properties']
        
        assert props['strictly_increasing'] is True
        assert props['domain'] == 'N > 0'
        assert props['continuous'] is True
        assert props['differentiable'] is True


class TestCompleteReport:
    """Tests para generación de reporte completo"""
    
    def test_generate_complete_report(self, analyzer):
        """Verificar que el reporte completo se genera sin errores."""
        report = analyzer.generate_complete_report()
        
        assert isinstance(report, str)
        assert len(report) > 1000
        
        # Verificar que contiene las secciones principales
        assert 'I. DEFINICIÓN FORMAL' in report
        assert 'II. PROPIEDADES BÁSICAS' in report
        assert 'III. INVERSA FORMAL' in report
        assert 'IV. DIFERENCIAS CON OTRAS BASES' in report
        assert 'V. ESTRUCTURA DE RESIDUOS' in report
        assert 'VI. ¿ESPECIALIDAD DE κ_Π(13)?' in report
        assert 'VII. CONCLUSIÓN ANALÍTICA' in report
    
    def test_report_contains_key_formulas(self, analyzer):
        """Verificar que el reporte contiene fórmulas clave."""
        report = analyzer.generate_complete_report()
        
        assert 'κ_Π(N) := ln(N) / ln(φ²)' in report
        assert 'd/dN κ_Π(N) = 1 / (N · ln(φ²))' in report
        assert 'N = (φ²)^x' in report


class TestVisualization:
    """Tests para visualización"""
    
    def test_plot_generation(self, analyzer, tmp_path):
        """Verificar que la visualización se genera correctamente."""
        import os
        
        save_path = str(tmp_path / "test_plot.png")
        result_path = analyzer.plot_complete_analysis(save_path=save_path)
        
        assert result_path == save_path
        assert os.path.exists(save_path)
        assert os.path.getsize(save_path) > 0


class TestIntegration:
    """Tests de integración con otros módulos"""
    
    def test_consistency_with_calabi_yau_kappa_pi(self, analyzer):
        """Verificar consistencia con módulo existente de Calabi-Yau."""
        # Importar módulo existente si está disponible
        try:
            from src.calabi_yau_kappa_pi_analysis import CalabiYauKappaAnalysis
            
            cy_analyzer = CalabiYauKappaAnalysis()
            
            # Comparar valores para varios N
            for N in [10, 12, 13, 14, 15]:
                kappa_new = analyzer.kappa_pi(N)
                kappa_old = cy_analyzer.kappa_pi(N)
                assert abs(kappa_new - kappa_old) < 1e-10
        except ImportError:
            pytest.skip("Módulo calabi_yau_kappa_pi_analysis no disponible")


class TestMathematicalRigor:
    """Tests adicionales de rigor matemático"""
    
    def test_logarithm_change_of_base(self, analyzer):
        """Verificar cambio de base logarítmica."""
        N = 13
        
        # κ_Π(N) = ln(N) / ln(φ²)
        kappa1 = analyzer.kappa_pi(N)
        
        # Debería ser igual a log_φ²(N)
        kappa2 = math.log(N) / math.log(analyzer.phi_squared)
        
        assert abs(kappa1 - kappa2) < 1e-15
    
    def test_phi_squared_golden_ratio_property(self, analyzer):
        """Verificar propiedad φ² = φ + 1."""
        assert abs(analyzer.phi_squared - (analyzer.phi + 1)) < 1e-15
    
    def test_continuity_at_point(self, analyzer):
        """Verificar continuidad en un punto."""
        N0 = 13
        epsilon = 1e-6
        
        kappa_N0 = analyzer.kappa_pi(N0)
        kappa_left = analyzer.kappa_pi(N0 - epsilon)
        kappa_right = analyzer.kappa_pi(N0 + epsilon)
        
        # Debe ser continua
        assert abs(kappa_left - kappa_N0) < 1e-5
        assert abs(kappa_right - kappa_N0) < 1e-5
    
    def test_limit_as_N_approaches_1(self, analyzer):
        """Verificar que κ_Π(1) = 0."""
        kappa_1 = analyzer.kappa_pi(1)
        assert abs(kappa_1 - 0) < 1e-15
    
    def test_asymptotic_behavior(self, analyzer):
        """Verificar comportamiento asintótico."""
        # Para N grandes, κ_Π(N) ≈ ln(N) / ln(φ²) crece sin límite
        N_large = [100, 1000, 10000]
        kappa_large = [analyzer.kappa_pi(N) for N in N_large]
        
        # Debe crecer
        for i in range(len(kappa_large) - 1):
            assert kappa_large[i] < kappa_large[i+1]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
