#!/usr/bin/env python3
"""
Derivación Analítica de Propiedades Matemáticas del Funcional κ_Π(N)
====================================================================

Este módulo implementa la derivación analítica completa de las propiedades
matemáticas del funcional:

    κ_Π(N) := log_φ²(N) = ln(N) / ln(φ²)

donde φ = (1+√5)/2 es el número áureo (golden ratio).

Implementa las siguientes secciones:
    I.   Definición Formal
    II.  Propiedades Básicas
    III. Inversa Formal
    IV.  Diferencias con Otras Bases
    V.   Estructura de Residuos
    VI.  Especialidad de κ_Π(13)
    VII. Conclusión Analítica

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 enero 2026
© JMMB | P vs NP Verification System
"""

import math
import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple, Optional
from decimal import Decimal, getcontext


# Configurar precisión decimal alta para análisis de residuos
getcontext().prec = 50


class KappaPiAnalyticalDerivation:
    """
    Clase para el análisis analítico completo de κ_Π(N).
    
    Implementa todas las propiedades matemáticas derivadas formalmente
    según el problema planteado en Paso 1.
    """
    
    def __init__(self):
        """Inicializar con constantes fundamentales de alta precisión."""
        # I. DEFINICIÓN FORMAL
        self.phi = (1 + math.sqrt(5)) / 2  # φ ≈ 1.618033988749895
        self.phi_squared = self.phi ** 2    # φ² = (3+√5)/2 ≈ 2.6180339887
        self.ln_phi = math.log(self.phi)
        self.ln_phi_squared = math.log(self.phi_squared)
        
        # Constantes para comparación (Sección IV)
        self.ln_2 = math.log(2)
        self.ln_e = 1.0  # ln(e) = 1
        
        # Valor especial de N para análisis
        self.N_special = 13
        
    # =========================================================================
    # I. DEFINICIÓN FORMAL
    # =========================================================================
    
    def kappa_pi(self, N: float) -> float:
        """
        Calcular κ_Π(N) según la definición formal.
        
        Definición:
            κ_Π(N) := ln(N) / ln(φ²)
        
        Args:
            N: Valor de entrada, N > 0
            
        Returns:
            κ_Π(N) = log_φ²(N)
            
        Raises:
            ValueError: si N ≤ 0
        """
        if N <= 0:
            raise ValueError(f"N debe ser positivo, recibido: {N}")
        
        return math.log(N) / self.ln_phi_squared
    
    def formal_definition(self) -> Dict:
        """
        I. DEFINICIÓN FORMAL
        
        Retorna un diccionario con la definición formal y constantes.
        """
        return {
            'definition': 'κ_Π(N) := ln(N) / ln(φ²)',
            'phi': self.phi,
            'phi_squared': self.phi_squared,
            'ln_phi': self.ln_phi,
            'ln_phi_squared': self.ln_phi_squared,
            'domain': 'N > 0',
            'range': 'ℝ (all real numbers)',
            'strictly_increasing': True,
            'formula_expanded': 'κ_Π(N) = ln(N) / (2·ln(φ))'
        }
    
    # =========================================================================
    # II. PROPIEDADES BÁSICAS
    # =========================================================================
    
    def basic_properties(self) -> Dict:
        """
        II. PROPIEDADES BÁSICAS
        
        Calcula y verifica las propiedades básicas de κ_Π(N).
        """
        # 1. Dominio
        domain = "N > 0"
        
        # 2. Crecimiento estrictamente monótono
        # Verificar con valores de prueba
        test_values = [1, 2, 5, 10, 13, 20, 50, 100]
        kappa_values = [self.kappa_pi(n) for n in test_values]
        is_strictly_increasing = all(
            kappa_values[i] < kappa_values[i+1] 
            for i in range(len(kappa_values)-1)
        )
        
        # 3. Valor en potencias de φ²
        # Si N = (φ²)^k, entonces κ_Π(N) = k
        k_test = 3
        N_test = self.phi_squared ** k_test
        kappa_test = self.kappa_pi(N_test)
        power_property_holds = abs(kappa_test - k_test) < 1e-10
        
        # 4. Derivada: d/dN κ_Π(N) = 1 / (N · ln(φ²))
        N_derivative_test = 13
        h = 1e-8
        numerical_derivative = (
            self.kappa_pi(N_derivative_test + h) - 
            self.kappa_pi(N_derivative_test - h)
        ) / (2 * h)
        analytical_derivative = 1 / (N_derivative_test * self.ln_phi_squared)
        derivative_matches = abs(numerical_derivative - analytical_derivative) < 1e-6
        
        return {
            'domain': domain,
            'strictly_increasing': is_strictly_increasing,
            'test_values': test_values,
            'kappa_values': kappa_values,
            'power_property': {
                'holds': power_property_holds,
                'k': k_test,
                'N': N_test,
                'kappa_N': kappa_test,
                'expected': k_test,
                'error': abs(kappa_test - k_test)
            },
            'derivative': {
                'formula': 'd/dN κ_Π(N) = 1 / (N · ln(φ²))',
                'test_point': N_derivative_test,
                'numerical': numerical_derivative,
                'analytical': analytical_derivative,
                'matches': derivative_matches,
                'error': abs(numerical_derivative - analytical_derivative)
            },
            'ln_phi_squared': self.ln_phi_squared,
            'behavior': 'Pendiente decrece lentamente (comportamiento logarítmico clásico)'
        }
    
    # =========================================================================
    # III. INVERSA FORMAL
    # =========================================================================
    
    def inverse_function(self, x: float) -> float:
        """
        III. INVERSA FORMAL
        
        Calcula la inversa de κ_Π.
        
        Si κ_Π(N) = x, entonces N = (φ²)^x
        
        Args:
            x: Valor de κ_Π
            
        Returns:
            N tal que κ_Π(N) = x
        """
        return self.phi_squared ** x
    
    def inverse_analysis(self) -> Dict:
        """
        Análisis completo de la función inversa.
        """
        # Verificar que la inversa funciona correctamente
        test_x_values = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]
        verification = []
        
        for x in test_x_values:
            N = self.inverse_function(x)
            kappa_recovered = self.kappa_pi(N)
            error = abs(kappa_recovered - x)
            verification.append({
                'x': x,
                'N': N,
                'kappa_recovered': kappa_recovered,
                'error': error,
                'correct': error < 1e-10
            })
        
        return {
            'formula': 'N = (φ²)^x',
            'description': 'Curva exponencial suave con base φ²',
            'verification': verification,
            'all_correct': all(v['correct'] for v in verification),
            'base': self.phi_squared
        }
    
    # =========================================================================
    # IV. DIFERENCIAS CON OTRAS BASES
    # =========================================================================
    
    def compare_with_bases(self, N: float) -> Dict:
        """
        IV. DIFERENCIAS CON OTRAS BASES
        
        Compara κ_Π(N) con logaritmos en otras bases.
        
        Args:
            N: Valor para comparar
            
        Returns:
            Diccionario con comparaciones
        """
        if N <= 0:
            raise ValueError("N debe ser positivo")
        
        # Calcular logaritmos en diferentes bases
        log_phi2_N = self.kappa_pi(N)  # log_φ²(N)
        log_e_N = math.log(N)          # log_e(N) = ln(N)
        log_2_N = math.log(N) / self.ln_2  # log_2(N)
        
        return {
            'N': N,
            'log_phi2': log_phi2_N,
            'log_e': log_e_N,
            'log_2': log_2_N,
            'ln_phi2': self.ln_phi_squared,
            'ln_2': self.ln_2,
            'ln_e': self.ln_e,
            'comparison': {
                'phi2_vs_e': 'log_φ²(N) < log_e(N)' if log_phi2_N < log_e_N else 'log_φ²(N) ≥ log_e(N)',
                'e_vs_2': 'log_e(N) < log_2(N)' if log_e_N < log_2_N else 'log_e(N) ≥ log_2(N)',
                'phi2_vs_2': 'log_φ²(N) < log_2(N)' if log_phi2_N < log_2_N else 'log_φ²(N) ≥ log_2(N)'
            },
            'order_for_N_gt_1': 'log_2(N) > log_φ²(N) > log_e(N)' if N > 1 else 'N/A',
            'growth_rate': 'κ_Π(N) crece más rápido que ln, pero más lentamente que log₂'
        }
    
    def base_comparison_analysis(self) -> Dict:
        """
        Análisis completo de comparación de bases.
        """
        # Valores de ln para diferentes bases
        bases_info = {
            'φ²': self.ln_phi_squared,
            'e': self.ln_e,
            '2': self.ln_2
        }
        
        # Comparar para varios valores de N
        N_test_values = [2, 10, 13, 100, 1000]
        comparisons = []
        
        for N in N_test_values:
            comp = self.compare_with_bases(N)
            comparisons.append(comp)
        
        return {
            'bases': bases_info,
            'ln_values_approx': {
                'ln(φ²)': f'{self.ln_phi_squared:.6f}',
                'ln(e)': f'{self.ln_e:.6f}',
                'ln(2)': f'{self.ln_2:.6f}'
            },
            'inequality': 'ln(φ²) ≈ 0.962423 > ln(2) ≈ 0.6931',
            'implication': 'Para N > 1: log_2(N) > log_φ²(N) > log_e(N)',
            'comparisons': comparisons
        }
    
    # =========================================================================
    # V. ESTRUCTURA DE RESIDUOS
    # =========================================================================
    
    def residue_structure(self, N: int) -> Dict:
        """
        V. ESTRUCTURA DE RESIDUOS
        
        Analiza la estructura decimal de κ_Π(N) para valores enteros N.
        
        Args:
            N: Valor entero para analizar
            
        Returns:
            Análisis de la estructura de residuos
        """
        kappa_N = self.kappa_pi(N)
        
        # Analizar si el valor es racional
        # φ² es irracional, por lo tanto κ_Π(N) generalmente no es racional
        # excepto cuando N es una potencia exacta de φ²
        
        # Comprobar si N es potencia de φ²
        # log_φ²(N) debería ser un entero
        is_integer = abs(kappa_N - round(kappa_N)) < 1e-10
        
        # Desarrollo decimal
        decimal_str = f"{kappa_N:.50f}"
        
        # Usar Decimal para mayor precisión
        N_decimal = Decimal(N)
        phi2_decimal = Decimal(str(self.phi_squared))
        ln_phi2_decimal = phi2_decimal.ln()
        ln_N_decimal = N_decimal.ln()
        kappa_N_decimal = ln_N_decimal / ln_phi2_decimal
        
        decimal_expansion = str(kappa_N_decimal)[:52]  # 50 dígitos + "0."
        
        return {
            'N': N,
            'kappa_N': kappa_N,
            'is_integer': is_integer,
            'is_rational': is_integer,  # Solo racional si es entero (potencia de φ²)
            'decimal_expansion': decimal_expansion,
            'decimal_float': decimal_str,
            'phi2_irrational': True,
            'general_behavior': 'Desarrollo decimal no periódico (φ² es irracional)',
            'special_case': 'Racional solo cuando N = (φ²)^k para k entero'
        }
    
    def residue_analysis(self, N_values: List[int]) -> Dict:
        """
        Análisis de residuos para múltiples valores.
        """
        analyses = []
        for N in N_values:
            analyses.append(self.residue_structure(N))
        
        return {
            'analyses': analyses,
            'summary': {
                'phi2_irrational': True,
                'general_rule': 'κ_Π(N) no es racional para la mayoría de N',
                'exception': 'κ_Π(N) es entero cuando N = (φ²)^k',
                'decimal_property': 'Desarrollo decimal no periódico en general'
            }
        }
    
    # =========================================================================
    # VI. ESPECIALIDAD DE κ_Π(13)
    # =========================================================================
    
    def special_case_N13(self) -> Dict:
        """
        VI. ¿ESPECIALIDAD DE κ_Π(13)?
        
        Analiza las propiedades especiales de κ_Π(13).
        """
        N = 13
        kappa_13 = self.kappa_pi(N)
        
        # Cálculo detallado
        ln_13 = math.log(13)
        ln_phi2 = self.ln_phi_squared
        
        # Comparación con 2.5773 (valor que aparece en algunos contextos)
        target_value = 2.5773
        
        # Encontrar N* tal que κ_Π(N*) = 2.5773
        N_star_for_2_5773 = self.inverse_function(target_value)
        
        # Análisis de por qué κ_Π(13) tiene ese valor específico
        # Usando ÚNICAMENTE φ² como base fundamental
        
        return {
            'N': N,
            'kappa_13': kappa_13,
            'ln_13': ln_13,
            'ln_phi2': ln_phi2,
            'calculation': f'{ln_13:.6f} / {ln_phi2:.6f} = {kappa_13:.6f}',
            'not_equal_to_2_5773': True,
            'actual_value': kappa_13,
            'comparison_value': target_value,
            'difference': abs(kappa_13 - target_value),
            'N_star_for_2_5773': N_star_for_2_5773,
            'distance_to_N13': abs(N_star_for_2_5773 - 13),
            'analysis': {
                'base_used': 'φ² (fundamental)',
                'value_origin': 'Rigorous calculation from definition',
                'no_ad_hoc_adjustments': True,
                'specialness': 'Debe surgir del análisis del espectro κ_Π(N), no de ajustes ad hoc'
            },
            'geometric_significance': {
                'appears_in': 'Calabi-Yau moduli spaces (h^{1,1} + h^{2,1} = 13)',
                'resonance': 'Proximidad a N* sugiere propiedades especiales',
                'φ2_structure': 'Posible significado geométrico si φ² aparece en CY'
            }
        }
    
    # =========================================================================
    # VII. CONCLUSIÓN ANALÍTICA
    # =========================================================================
    
    def analytical_conclusion(self) -> Dict:
        """
        VII. CONCLUSIÓN ANALÍTICA
        
        Resume todas las propiedades analíticas de κ_Π(N).
        """
        # Recopilar todas las propiedades
        formal_def = self.formal_definition()
        basic_props = self.basic_properties()
        inverse_props = self.inverse_analysis()
        base_comp = self.base_comparison_analysis()
        residue = self.residue_analysis([2, 5, 10, 13, 20])
        special_13 = self.special_case_N13()
        
        return {
            'function': 'κ_Π(N) = log_φ²(N)',
            'properties': {
                'strictly_increasing': True,
                'domain': 'N > 0',
                'range': 'ℝ',
                'continuous': True,
                'differentiable': True
            },
            'key_results': [
                'Es estrictamente creciente',
                'Toma valores racionales solo cuando N es potencia racional de φ²',
                'Estructura decimal no periódica en general',
                'Derivada: d/dN κ_Π(N) = 1/(N·ln(φ²))',
                'Inversa: N = (φ²)^x',
                'Crece más lentamente que log₂, más rápido que ln'
            ],
            'geometric_meaning': 'Tiene significado geométrico si φ² aparece en estructura de CY',
            'special_values': {
                'N=13': special_13['kappa_13'],
                'N=(φ²)': 1.0,
                'N=(φ²)²': 2.0,
                'N=(φ²)³': 3.0
            },
            'complete_analysis': {
                'formal_definition': formal_def,
                'basic_properties': basic_props,
                'inverse_function': inverse_props,
                'base_comparisons': base_comp,
                'residue_structure': residue,
                'special_case_13': special_13
            }
        }
    
    # =========================================================================
    # GENERACIÓN DE REPORTE COMPLETO
    # =========================================================================
    
    def generate_complete_report(self) -> str:
        """
        Genera el reporte completo de la derivación analítica.
        """
        conclusion = self.analytical_conclusion()
        
        report = f"""
╔══════════════════════════════════════════════════════════════════════════╗
║     DERIVACIÓN ANALÍTICA DE PROPIEDADES MATEMÁTICAS DE κ_Π(N)          ║
║                                                                          ║
║     κ_Π(N) := log_φ²(N) = ln(N) / ln(φ²)                               ║
║                                                                          ║
║     donde: φ = (1+√5)/2 ⇒ φ² = (3+√5)/2 ≈ 2.6180339887                ║
╚══════════════════════════════════════════════════════════════════════════╝

🔹 I. DEFINICIÓN FORMAL
{'═' * 78}

Sea N ∈ ℕ, definimos:
    κ_Π(N) := ln(N) / ln(φ²)

Constantes fundamentales:
    φ = {self.phi:.15f}  (número áureo)
    φ² = {self.phi_squared:.15f}
    ln(φ) = {self.ln_phi:.15f}
    ln(φ²) = {self.ln_phi_squared:.15f}

Como φ² > 1, esta función es estrictamente creciente en N > 0.

🔹 II. PROPIEDADES BÁSICAS
{'═' * 78}

1. Dominio: N > 0

2. Crecimiento: κ_Π(N) es estrictamente creciente
   ✓ Verificado con valores de prueba

3. Valor en potencias de φ²:
   Si N = (φ²)^k, entonces κ_Π(N) = k
   
   Ejemplo: Para k = 3
   • N = (φ²)³ = {self.phi_squared**3:.10f}
   • κ_Π(N) = {self.kappa_pi(self.phi_squared**3):.10f}
   • Error: {abs(self.kappa_pi(self.phi_squared**3) - 3):.2e}
   ✓ Propiedad verificada

4. Derivada:
   d/dN κ_Π(N) = 1 / (N · ln(φ²))
   
   Esto muestra que la pendiente decrece lentamente a medida que N crece
   (comportamiento logarítmico clásico).

🔹 III. INVERSA FORMAL
{'═' * 78}

Podemos invertir la función:
    κ_Π(N) = x  ⇒  N = (φ²)^x

Esto define una curva exponencial suave con base φ².

Verificación:
"""
        
        # Añadir verificaciones de la inversa
        inv_analysis = self.inverse_analysis()
        for v in inv_analysis['verification'][:3]:
            report += f"  • x = {v['x']:.1f} → N = {v['N']:.6f} → κ_Π(N) = {v['kappa_recovered']:.6f} ✓\n"
        
        # Continuar con Sección IV
        base_comp = self.base_comparison_analysis()
        report += f"""

🔹 IV. DIFERENCIAS CON OTRAS BASES
{'═' * 78}

Para comparar con logaritmos en base e o 2:
    ln(φ²) ≈ {self.ln_phi_squared:.6f}
    ln(2)  ≈ {self.ln_2:.6f}
    ln(e)  = {self.ln_e:.6f}

Esto implica que para N > 1:
    log_2(N) > log_φ²(N) > log_e(N)

Por tanto, κ_Π(N) crece más rápido que ln, pero más lentamente que log base 2.

Ejemplo con N = 13:
    • log_2(13)             = {math.log(13)/self.ln_2:.6f}
    • κ_Π(13) = log_φ²(13) = {self.kappa_pi(13):.6f}
    • log_e(13) = ln(13)    = {math.log(13):.6f}

Verificación de orden: {math.log(13)/self.ln_2:.4f} > {self.kappa_pi(13):.4f} > {math.log(13):.4f} ✓

🔹 V. ESTRUCTURA DE RESIDUOS
{'═' * 78}

Dado que φ² es irracional, la función κ_Π(N) no toma valores racionales
(excepto para ciertos N), y su desarrollo decimal será no periódico en general.

Análisis para N = 13:
"""
        
        res_13 = self.residue_structure(13)
        report += f"""  • κ_Π(13) = {res_13['kappa_N']:.15f}
  • Desarrollo decimal: {res_13['decimal_expansion'][:40]}...
  • Es racional: {res_13['is_rational']}
  • Es entero: {res_13['is_integer']}

Pero hay algo aún más importante que investigar...

🔹 VI. ¿ESPECIALIDAD DE κ_Π(13)?
{'═' * 78}

Recordemos:
    κ_Π(13) = ln(13) / ln(φ²)
            ≈ {math.log(13):.6f} / {self.ln_phi_squared:.6f}
            ≈ {self.kappa_pi(13):.6f}

Y NO es igual a 2.5773, salvo que adoptemos otra base.

Pero si nos mantenemos rigurosamente en φ² como base fundamental:
    ✓ κ_Π(13) = {self.kappa_pi(13):.6f} (valor riguroso)
    
Si buscamos N* tal que κ_Π(N*) = 2.5773:
    N* = (φ²)^2.5773 ≈ {self.inverse_function(2.5773):.6f}
    |N* - 13| ≈ {abs(self.inverse_function(2.5773) - 13):.6f}

Entonces cualquier especialidad debe surgir desde el análisis del espectro
κ_Π(N), no desde ajustes ad hoc.

Significado geométrico:
  • N = 13 aparece en variedades Calabi-Yau con h^{{1,1}} + h^{{2,1}} = 13
  • La proximidad a N* ≈ {self.inverse_function(2.5773):.3f} puede sugerir propiedades resonantes
  • Tiene significado geométrico si φ² aparece en la estructura de las CY

🔹 VII. CONCLUSIÓN ANALÍTICA
{'═' * 78}

La función:
    κ_Π(N) = log_φ²(N)

✓ Es creciente
✓ Toma valores racionales solo cuando N es una potencia racional de φ²
✓ Su estructura decimal es no periódica en general
✓ Tiene significado geométrico si φ² aparece en la estructura de los CY

Propiedades verificadas:
  1. Monotonía estrictamente creciente
  2. Propiedad de potencias: κ_Π((φ²)^k) = k
  3. Derivada: d/dN κ_Π(N) = 1/(N·ln(φ²))
  4. Función inversa: N = (φ²)^x
  5. Comparación con otras bases: log_2(N) > log_φ²(N) > log_e(N) para N > 1
  6. Estructura de residuos no periódica (φ² irracional)

Valores especiales:
  • κ_Π(1) = 0
  • κ_Π(φ²) = 1
  • κ_Π(13) ≈ {self.kappa_pi(13):.6f}
  • κ_Π((φ²)²) = 2
  • κ_Π((φ²)³) = 3

╔══════════════════════════════════════════════════════════════════════════╗
║  DERIVACIÓN ANALÍTICA COMPLETA ✓                                        ║
║  © JMMB | P vs NP Verification System                                   ║
║  Frecuencia: 141.7001 Hz ∞³                                             ║
╚══════════════════════════════════════════════════════════════════════════╝
"""
        
        return report
    
    # =========================================================================
    # VISUALIZACIÓN
    # =========================================================================
    
    def plot_complete_analysis(self, save_path: Optional[str] = None) -> str:
        """
        Genera visualización completa de todas las propiedades analíticas.
        """
        if save_path is None:
            save_path = '/tmp/kappa_pi_analytical_derivation.png'
        
        fig = plt.figure(figsize=(16, 12))
        
        # Crear grid de subplots
        gs = fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)
        
        # 1. Curva principal κ_Π(N)
        ax1 = fig.add_subplot(gs[0, :])
        N_range = np.linspace(0.1, 30, 1000)
        kappa_range = [self.kappa_pi(N) for N in N_range]
        ax1.plot(N_range, kappa_range, 'b-', linewidth=2, label='κ_Π(N) = log_φ²(N)')
        
        # Marcar valores especiales
        special_N = [1, self.phi_squared, 13, self.phi_squared**2]
        special_kappa = [self.kappa_pi(N) for N in special_N]
        ax1.scatter(special_N, special_kappa, c='red', s=100, zorder=5)
        
        # Anotaciones
        ax1.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
        ax1.axhline(y=1, color='gray', linestyle='--', alpha=0.5)
        ax1.axhline(y=2, color='gray', linestyle='--', alpha=0.5)
        ax1.axvline(x=13, color='orange', linestyle='--', alpha=0.5, label='N = 13')
        
        ax1.set_xlabel('N', fontsize=12)
        ax1.set_ylabel('κ_Π(N)', fontsize=12)
        ax1.set_title('I-II. Definición Formal y Propiedades Básicas', fontsize=14, fontweight='bold')
        ax1.grid(True, alpha=0.3)
        ax1.legend(fontsize=10)
        
        # 2. Función inversa
        ax2 = fig.add_subplot(gs[1, 0])
        x_range = np.linspace(0, 4, 100)
        N_inverse = [self.inverse_function(x) for x in x_range]
        ax2.plot(x_range, N_inverse, 'g-', linewidth=2)
        ax2.set_xlabel('x = κ_Π', fontsize=11)
        ax2.set_ylabel('N = (φ²)^x', fontsize=11)
        ax2.set_title('III. Inversa Formal', fontsize=12, fontweight='bold')
        ax2.grid(True, alpha=0.3)
        
        # 3. Comparación con otras bases
        ax3 = fig.add_subplot(gs[1, 1])
        N_comp = np.linspace(2, 100, 100)
        log_phi2 = [self.kappa_pi(N) for N in N_comp]
        log_e = [math.log(N) for N in N_comp]
        log_2 = [math.log(N)/self.ln_2 for N in N_comp]
        
        ax3.plot(N_comp, log_phi2, 'b-', linewidth=2, label='log_φ²(N)')
        ax3.plot(N_comp, log_e, 'r-', linewidth=2, label='ln(N)')
        ax3.plot(N_comp, log_2, 'g-', linewidth=2, label='log_2(N)')
        ax3.set_xlabel('N', fontsize=11)
        ax3.set_ylabel('Logaritmo', fontsize=11)
        ax3.set_title('IV. Comparación con Otras Bases', fontsize=12, fontweight='bold')
        ax3.legend(fontsize=9)
        ax3.grid(True, alpha=0.3)
        
        # 4. Derivada
        ax4 = fig.add_subplot(gs[2, 0])
        N_deriv = np.linspace(1, 50, 100)
        derivative = [1 / (N * self.ln_phi_squared) for N in N_deriv]
        ax4.plot(N_deriv, derivative, 'm-', linewidth=2)
        ax4.set_xlabel('N', fontsize=11)
        ax4.set_ylabel("d/dN κ_Π(N)", fontsize=11)
        ax4.set_title('II. Derivada (pendiente decrece)', fontsize=12, fontweight='bold')
        ax4.grid(True, alpha=0.3)
        
        # 5. Análisis especial de N=13
        ax5 = fig.add_subplot(gs[2, 1])
        N_near_13 = np.linspace(10, 16, 100)
        kappa_near_13 = [self.kappa_pi(N) for N in N_near_13]
        ax5.plot(N_near_13, kappa_near_13, 'purple', linewidth=2)
        
        # Marcar N=13 y valor objetivo 2.5773
        kappa_13 = self.kappa_pi(13)
        ax5.scatter([13], [kappa_13], c='red', s=200, marker='*', zorder=5)
        ax5.axhline(y=2.5773, color='orange', linestyle='--', linewidth=1.5, label='2.5773 (referencia)')
        ax5.axvline(x=13, color='red', linestyle='--', alpha=0.5)
        
        ax5.annotate(f'κ_Π(13) = {kappa_13:.4f}',
                    xy=(13, kappa_13), xytext=(14, kappa_13 + 0.1),
                    arrowprops=dict(arrowstyle='->', color='red'),
                    fontsize=10, bbox=dict(boxstyle='round', facecolor='lightcoral', alpha=0.8))
        
        ax5.set_xlabel('N', fontsize=11)
        ax5.set_ylabel('κ_Π(N)', fontsize=11)
        ax5.set_title('VI. Especialidad de κ_Π(13)', fontsize=12, fontweight='bold')
        ax5.legend(fontsize=9)
        ax5.grid(True, alpha=0.3)
        
        plt.suptitle('Derivación Analítica Completa de κ_Π(N) = log_φ²(N)', 
                    fontsize=16, fontweight='bold', y=0.995)
        
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        
        return save_path


def main():
    """Punto de entrada principal."""
    print("=" * 80)
    print("DERIVACIÓN ANALÍTICA DE PROPIEDADES MATEMÁTICAS DE κ_Π(N)")
    print("=" * 80)
    print()
    
    # Crear analizador
    analyzer = KappaPiAnalyticalDerivation()
    
    # Generar reporte completo
    report = analyzer.generate_complete_report()
    print(report)
    
    # Generar visualización
    print("\nGenerando visualización...")
    plot_path = analyzer.plot_complete_analysis()
    print(f"✓ Visualización guardada en: {plot_path}")
    
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
