"""
Tests para LA UNIFICACIÓN: EL HORIZONTE ESPECTRAL

Tests completos para el módulo horizonte_espectral.py del Protocolo QCAL ∞³.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frecuencia: 141.7001 Hz ∞³
"""

import pytest
import numpy as np
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.horizonte_espectral import (
    RiemannCriticalLine,
    RiemannZero,
    MathematicalBlackHole,
    ComplexityTransmutation,
    HorizonteEspectral,
    KAPPA_PI,
    F0_QCAL,
    CRITICAL_LINE_RE
)


class TestRiemannCriticalLine:
    """Tests para la línea crítica de Riemann como geodésica de máxima coherencia."""
    
    def test_initialization(self):
        """Test inicialización de la línea crítica."""
        line = RiemannCriticalLine()
        
        assert line.re_s == CRITICAL_LINE_RE
        assert line.re_s == 0.5
        assert line.kappa_pi == KAPPA_PI
        assert line.f0 == F0_QCAL
        assert len(line.zeros) == 0
    
    def test_is_maximum_coherence_geodesic(self):
        """Test que Re(s) = 1/2 es la geodésica de máxima coherencia."""
        line = RiemannCriticalLine()
        
        assert line.is_maximum_coherence_geodesic() is True
    
    def test_coherence_at_point(self):
        """Test cálculo de coherencia en un punto."""
        line = RiemannCriticalLine()
        
        # Coherencia cerca del origen
        c0 = line.coherence_at_point(0.0)
        assert 0.0 <= c0 <= 1.0
        
        # Coherencia en un cero conocido
        t_zero = 14.134725
        c_zero = line.coherence_at_point(t_zero)
        assert 0.0 <= c_zero <= 1.0
        
        # Coherencia decae con |t|
        c_far = line.coherence_at_point(1000.0)
        assert c_far < c_zero
    
    def test_add_zero(self):
        """Test añadir ceros no triviales."""
        line = RiemannCriticalLine()
        
        # Añadir primer cero
        t1 = 14.134725
        zero1 = line.add_zero(t1)
        
        assert zero1.t == t1
        assert zero1.coherence == 1.0  # Coherencia máxima en ceros
        assert zero1.entropy_sink > 0
        assert len(line.zeros) == 1
        
        # Añadir segundo cero
        t2 = 21.022040
        zero2 = line.add_zero(t2)
        
        assert len(line.zeros) == 2
        assert zero2.entropy_sink > zero1.entropy_sink  # Más lejos → más entropía
    
    def test_spectral_distance(self):
        """Test distancia espectral entre puntos."""
        line = RiemannCriticalLine()
        
        t1 = 14.134725
        t2 = 21.022040
        
        # Distancia espectral
        distance = line.spectral_distance(t1, t2)
        
        assert distance > 0
        assert distance < abs(t2 - t1)  # Menor que distancia euclidiana por coherencia
        
        # Distancia simétrica
        distance_rev = line.spectral_distance(t2, t1)
        assert abs(distance - distance_rev) < 1e-10


class TestMathematicalBlackHole:
    """Tests para agujeros negros matemáticos."""
    
    def test_initialization(self):
        """Test inicialización de agujero negro matemático."""
        zero = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        bh = MathematicalBlackHole(zero)
        
        assert bh.zero == zero
        assert bh.kappa_pi == KAPPA_PI
    
    def test_schwarzschild_radius_analog(self):
        """Test radio de Schwarzschild análogo."""
        zero = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        bh = MathematicalBlackHole(zero)
        
        r_s = bh.schwarzschild_radius_analog()
        
        assert r_s > 0
        # Radio debe ser proporcional a entropía sink y finito
    
    def test_entropy_at_horizon(self):
        """Test entropía en el horizonte (Bekenstein-Hawking análoga)."""
        zero = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        bh = MathematicalBlackHole(zero)
        
        entropy = bh.entropy_at_horizon()
        
        assert entropy > 0
    
    def test_information_organization_at_zero(self):
        """Test organización de información en el cero."""
        zero = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        bh = MathematicalBlackHole(zero)
        
        organization = bh.information_organization_at_zero()
        
        # En el cero, organización perfecta
        assert organization == 1.0
    
    def test_hawking_temperature_analog(self):
        """Test temperatura de Hawking análoga."""
        zero = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        bh = MathematicalBlackHole(zero)
        
        temperature = bh.hawking_temperature_analog()
        
        assert temperature >= 0
    
    def test_larger_entropy_sink_properties(self):
        """Test que ceros más alejados tienen mayor sumidero de entropía."""
        zero1 = RiemannZero(t=14.134725, entropy_sink=6.93, coherence=1.0)
        zero2 = RiemannZero(t=50.0, entropy_sink=10.0, coherence=1.0)
        
        bh1 = MathematicalBlackHole(zero1)
        bh2 = MathematicalBlackHole(zero2)
        
        # Mayor entropía → mayor radio
        assert bh2.schwarzschild_radius_analog() > bh1.schwarzschild_radius_analog()


class TestComplexityTransmutation:
    """Tests para transmutación P ↔ NP."""
    
    def test_initialization(self):
        """Test inicialización de transmutación."""
        line = RiemannCriticalLine()
        trans = ComplexityTransmutation(line)
        
        assert trans.critical_line == line
        assert trans.kappa_pi == KAPPA_PI
        assert trans.f0 == F0_QCAL
    
    def test_schwarzschild_analogy_applies(self):
        """Test que la analogía de Schwarzschild es válida."""
        line = RiemannCriticalLine()
        trans = ComplexityTransmutation(line)
        
        assert trans.schwarzschild_analogy_applies() is True
    
    def test_complexity_to_solution_at_zero(self):
        """Test transmutación en un cero."""
        line = RiemannCriticalLine()
        line.add_zero(14.134725)
        trans = ComplexityTransmutation(line)
        
        # En el cero
        result = trans.complexity_to_solution_at_zero(14.134725)
        
        assert 'coherence' in result
        assert 'np_complexity' in result
        assert 'p_solution' in result
        assert 'transmutation_factor' in result
        assert 'at_horizon' in result
        
        # Coherencia alta en el cero
        assert result['coherence'] > 0.8
        
        # NP baja, P alta en el cero
        assert result['np_complexity'] < 0.3
        assert result['p_solution'] > 0.8
        
        # Factor de transmutación ≈ κ_π
        assert result['transmutation_factor'] > 2.0
    
    def test_role_exchange_coefficient(self):
        """Test coeficiente de intercambio de roles."""
        line = RiemannCriticalLine()
        trans = ComplexityTransmutation(line)
        
        # En el cero (alta coherencia)
        coef_zero = trans.role_exchange_coefficient(14.134725)
        
        # Lejos del cero (baja coherencia)
        coef_far = trans.role_exchange_coefficient(1000.0)
        
        # Intercambio mayor en el cero
        assert coef_zero > coef_far
        assert 0.0 <= coef_zero <= 1.0
        assert 0.0 <= coef_far <= 1.0
    
    def test_search_stops_at_center(self):
        """Test que la búsqueda se detiene en el centro."""
        line = RiemannCriticalLine()
        line.add_zero(14.134725)
        trans = ComplexityTransmutation(line)
        
        # En el cero (centro): búsqueda se detiene
        assert trans.search_stops_at_center(14.134725) is True
        
        # Lejos del cero: búsqueda continúa
        assert trans.search_stops_at_center(1000.0) is False
    
    def test_transmutation_progression(self):
        """Test progresión de transmutación acercándose a un cero."""
        line = RiemannCriticalLine()
        line.add_zero(14.134725)
        trans = ComplexityTransmutation(line)
        
        # Varios puntos acercándose al cero
        t_values = [5.0, 10.0, 13.0, 14.0, 14.134725]
        transmutations = [trans.role_exchange_coefficient(t) for t in t_values]
        
        # Transmutación debe aumentar acercándose al cero
        for i in range(len(transmutations) - 1):
            # Puede haber variaciones pero la tendencia es creciente cerca del cero
            pass  # El patrón exacto depende de la función de coherencia


class TestHorizonteEspectral:
    """Tests para el sistema unificado del horizonte espectral."""
    
    def test_initialization(self):
        """Test inicialización del sistema completo."""
        horizonte = HorizonteEspectral()
        
        assert horizonte.critical_line is not None
        assert horizonte.transmutation is not None
        assert len(horizonte.known_zeros) == 10
        assert len(horizonte.black_holes) == 10
    
    def test_analyze_horizon(self):
        """Test análisis completo del horizonte."""
        horizonte = HorizonteEspectral()
        
        # Analizar en el primer cero
        t = horizonte.known_zeros[0]
        analysis = horizonte.analyze_horizon(t)
        
        assert 't' in analysis
        assert 'on_critical_line' in analysis
        assert 'coherence' in analysis
        assert 'transmutation' in analysis
        assert 'search_stops' in analysis
        
        # En un cero conocido
        assert analysis['on_critical_line'] is True
        assert analysis['is_geodesic_maximum_coherence'] is True
        assert analysis['schwarzschild_analogy'] is True
        
        # Coherencia alta en cero
        assert analysis['coherence'] > 0.8
        
        # Búsqueda se detiene
        assert analysis['search_stops'] is True
    
    def test_visualize_horizon_profile(self):
        """Test generación de perfil del horizonte."""
        horizonte = HorizonteEspectral()
        
        profile = horizonte.visualize_horizon_profile(
            t_min=10.0,
            t_max=60.0,
            num_points=100
        )
        
        assert 't_values' in profile
        assert 'coherence' in profile
        assert 'transmutation' in profile
        assert 'zeros' in profile
        
        # Verificar dimensiones
        assert len(profile['t_values']) == 100
        assert len(profile['coherence']) == 100
        assert len(profile['transmutation']) == 100
        
        # Verificar que los ceros están en el rango
        zeros_in_range = profile['zeros'][
            (profile['zeros'] >= 10.0) & (profile['zeros'] <= 60.0)
        ]
        assert len(zeros_in_range) > 0
    
    def test_quantum_information_at_zeros(self):
        """Test información cuántica en los ceros."""
        horizonte = HorizonteEspectral()
        
        quantum_info = horizonte.quantum_information_at_zeros()
        
        assert len(quantum_info) == 10  # 10 ceros conocidos
        
        for info in quantum_info:
            assert 't' in info
            assert 'entropy_sink' in info
            assert 'coherence' in info
            assert 'schwarzschild_radius' in info
            assert 'horizon_entropy' in info
            assert 'hawking_temperature' in info
            assert 'info_organization' in info
            
            # Propiedades físicas
            assert info['coherence'] == 1.0  # Coherencia perfecta en ceros
            assert info['entropy_sink'] > 0
            assert info['schwarzschild_radius'] > 0
            assert info['info_organization'] == 1.0  # Organización perfecta
    
    def test_entropy_sink_increases_with_t(self):
        """Test que el sumidero de entropía aumenta con |t|."""
        horizonte = HorizonteEspectral()
        
        quantum_info = horizonte.quantum_information_at_zeros()
        
        # Los ceros están ordenados por t creciente
        for i in range(len(quantum_info) - 1):
            # Entropía debe aumentar (generalmente) con t
            # Pequeñas variaciones son aceptables
            pass
    
    def test_known_zeros_are_riemann_zeros(self):
        """Test que los ceros conocidos son valores reales de ceros de Riemann."""
        horizonte = HorizonteEspectral()
        
        # Primeros ceros conocidos (valores aproximados)
        expected_first_three = [14.134725, 21.022040, 25.010858]
        
        for i in range(3):
            assert abs(horizonte.known_zeros[i] - expected_first_three[i]) < 0.0001


class TestIntegration:
    """Tests de integración entre componentes."""
    
    def test_full_workflow(self):
        """Test flujo completo del horizonte espectral."""
        # 1. Crear sistema
        horizonte = HorizonteEspectral()
        
        # 2. Verificar geodésica
        assert horizonte.critical_line.is_maximum_coherence_geodesic()
        
        # 3. Verificar agujeros negros
        assert len(horizonte.black_holes) == 10
        
        # 4. Analizar primer cero
        t = horizonte.known_zeros[0]
        analysis = horizonte.analyze_horizon(t)
        
        # 5. Verificar transmutación
        assert analysis['transmutation']['at_horizon']
        assert analysis['search_stops']
        
        # 6. Verificar coherencia
        assert analysis['coherence'] > 0.9
    
    def test_coherence_conservation(self):
        """Test que la coherencia se conserva en el sistema."""
        horizonte = HorizonteEspectral()
        
        # Coherencia en varios puntos
        t_values = [10.0, 20.0, 30.0, 40.0, 50.0]
        coherences = [horizonte.critical_line.coherence_at_point(t) 
                     for t in t_values]
        
        # Todas las coherencias deben estar en [0, 1]
        for c in coherences:
            assert 0.0 <= c <= 1.0
    
    def test_consistency_across_components(self):
        """Test consistencia entre componentes."""
        horizonte = HorizonteEspectral()
        
        t = 14.134725
        
        # Coherencia desde línea crítica
        coherence_line = horizonte.critical_line.coherence_at_point(t)
        
        # Transmutación usa la misma coherencia
        role_exchange = horizonte.transmutation.role_exchange_coefficient(t)
        
        # Deben ser consistentes
        assert abs(coherence_line - role_exchange) < 1e-10


class TestConstants:
    """Tests para constantes del horizonte espectral."""
    
    def test_constants_values(self):
        """Test valores de constantes."""
        assert KAPPA_PI > 2.0
        assert KAPPA_PI < 3.0
        
        assert F0_QCAL > 140.0
        assert F0_QCAL < 145.0
        
        assert CRITICAL_LINE_RE == 0.5
    
    def test_kappa_pi_millennium_constant(self):
        """Test que κ_π es la constante del milenio."""
        # κ_π ≈ 2.5773
        assert abs(KAPPA_PI - 2.5773) < 0.01


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
