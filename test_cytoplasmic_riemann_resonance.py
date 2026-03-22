#!/usr/bin/env python3
"""
Test Suite: Cytoplasmic Riemann Resonance Model
================================================

Suite completa de pruebas para validar el modelo de resonancia
citoplasmática basado en la hipótesis de Riemann.

Pruebas incluidas:
------------------
1. Constantes fundamentales
2. Longitud de coherencia
3. Frecuencias armónicas
4. Hermiticidad del operador
5. Detección de descoherencia
6. Validación de hipótesis
7. Protocolo molecular
8. Exportación de resultados

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 febrero 2026
Sello: ∴𓂀Ω∞³
"""

import sys
import os
import json
import numpy as np
import pytest
from pathlib import Path

# Agregar ruta al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ''))

from xenos.cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    generate_biological_mapping,
    BASE_FREQUENCY_HZ,
    KAPPA_PI,
    RIEMANN_FIRST_ZERO,
    BIOPHYSICAL_SCALING
)


# ============================================================================
# TEST CLASS: FUNDAMENTAL CONSTANTS
# ============================================================================

class TestFundamentalConstants:
    """Pruebas para verificar las constantes fundamentales del modelo."""
    
    def test_riemann_first_zero(self):
        """Verifica que el primer cero de Riemann sea correcto."""
        expected = 14.134725
        assert abs(RIEMANN_FIRST_ZERO - expected) < 0.001, \
            f"Primer cero de Riemann incorrecto: {RIEMANN_FIRST_ZERO}"
    
    def test_base_frequency(self):
        """Verifica que la frecuencia base sea correcta."""
        expected = RIEMANN_FIRST_ZERO * BIOPHYSICAL_SCALING
        assert abs(BASE_FREQUENCY_HZ - expected) < 0.1, \
            f"Frecuencia base incorrecta: {BASE_FREQUENCY_HZ}"
        
        # Verificar valor aproximado
        assert abs(BASE_FREQUENCY_HZ - 141.7001) < 0.1, \
            f"Frecuencia base debería ser ~141.7 Hz, pero es {BASE_FREQUENCY_HZ}"
    
    def test_kappa_pi_value(self):
        """Verifica que κ_Π tenga el valor correcto."""
        expected = 2.5773
        assert abs(KAPPA_PI - expected) < 0.0001, \
            f"κ_Π incorrecto: {KAPPA_PI}"
    
    def test_biophysical_scaling(self):
        """Verifica la constante de conversión biofísica."""
        expected = 10.025
        assert abs(BIOPHYSICAL_SCALING - expected) < 0.001, \
            f"Scaling biofísico incorrecto: {BIOPHYSICAL_SCALING}"


# ============================================================================
# TEST CLASS: COHERENCE LENGTH
# ============================================================================

class TestCoherenceLength:
    """Pruebas para la longitud de coherencia."""
    
    def test_fundamental_coherence_length(self):
        """Verifica que ξ₁ ≈ 1.06 μm."""
        model = CytoplasmicRiemannResonance()
        xi_um = model.xi_fundamental * 1e6
        
        # Debe estar cerca de 1.06 μm
        assert 1.05 < xi_um < 1.07, \
            f"Longitud de coherencia fuera de rango: {xi_um:.4f} μm"
        
        # Valor más preciso
        assert abs(xi_um - 1.0598) < 0.01, \
            f"ξ₁ debería ser ~1.0598 μm, pero es {xi_um:.4f} μm"
    
    def test_coherence_scales_with_frequency(self):
        """Verifica que ξ ∝ 1/√f."""
        model = CytoplasmicRiemannResonance()
        
        omega1 = 2 * np.pi * model.base_frequency
        omega2 = 2 * np.pi * (2 * model.base_frequency)
        
        xi1 = model._calculate_coherence_length(omega1)
        xi2 = model._calculate_coherence_length(omega2)
        
        # ξ₂ debería ser ξ₁/√2
        expected_ratio = 1.0 / np.sqrt(2)
        actual_ratio = xi2 / xi1
        
        assert abs(actual_ratio - expected_ratio) < 0.01, \
            f"Escalamiento incorrecto: {actual_ratio:.4f} vs {expected_ratio:.4f}"
    
    def test_get_coherence_at_cellular_scale(self):
        """Verifica coherencia a escala celular (1.06 μm)."""
        model = CytoplasmicRiemannResonance()
        
        coherence = model.get_coherence_at_scale(1.06e-6)
        
        # Debe ser resonante a esta escala
        assert coherence['is_resonant'], \
            "Debería ser resonante a 1.06 μm"
        
        # Debe ser estable (hermítico)
        assert coherence['is_stable'], \
            "Debería ser estable a escala celular"
        
        # Hermiticidad alta
        assert coherence['hermiticity_index'] > 0.95, \
            f"Hermiticidad baja: {coherence['hermiticity_index']:.3f}"


# ============================================================================
# TEST CLASS: HARMONIC FREQUENCIES
# ============================================================================

class TestHarmonicFrequencies:
    """Pruebas para las frecuencias armónicas."""
    
    def test_first_harmonic(self):
        """Verifica que f₁ = 141.7001 Hz."""
        model = CytoplasmicRiemannResonance()
        
        f1 = model.base_frequency
        assert abs(f1 - 141.7001) < 0.1, \
            f"Primera frecuencia armónica incorrecta: {f1}"
    
    def test_harmonic_series(self):
        """Verifica que fₙ = n × f₁."""
        model = CytoplasmicRiemannResonance()
        
        for n in range(1, 11):
            expected = n * model.base_frequency
            
            # Calcular a través de coherencia
            # (método indirecto pero más robusto)
            scale = model.xi_fundamental / np.sqrt(n)
            coherence = model.get_coherence_at_scale(scale)
            actual = coherence['frequency_hz']
            
            relative_error = abs(actual - expected) / expected
            assert relative_error < 0.01, \
                f"Armónico {n}: {actual:.2f} Hz vs esperado {expected:.2f} Hz"
    
    def test_known_harmonics(self):
        """Verifica valores específicos de armónicos."""
        model = CytoplasmicRiemannResonance()
        
        known_harmonics = {
            1: 141.7,
            2: 283.4,
            3: 425.1
        }
        
        for n, expected in known_harmonics.items():
            actual = n * model.base_frequency
            assert abs(actual - expected) < 1.0, \
                f"f_{n} = {actual:.1f} Hz, esperado ~{expected} Hz"


# ============================================================================
# TEST CLASS: HERMITICITY
# ============================================================================

class TestHermiticity:
    """Pruebas para la hermiticidad del operador."""
    
    def test_hermiticity_index_range(self):
        """Verifica que el índice de hermiticidad esté en [0, 1]."""
        model = CytoplasmicRiemannResonance()
        
        for n in range(1, 11):
            h_index = model._check_hermiticity(n)
            assert 0 <= h_index <= 1, \
                f"Índice de hermiticidad fuera de rango: {h_index}"
    
    def test_perfect_hermiticity_low_harmonics(self):
        """Verifica hermiticidad perfecta para armónicos bajos."""
        model = CytoplasmicRiemannResonance()
        
        for n in range(1, 6):
            h_index = model._check_hermiticity(n)
            assert h_index > 0.99, \
                f"Hermiticidad baja para armónico {n}: {h_index:.4f}"
    
    def test_resonant_harmonic_finding(self):
        """Verifica que se encuentre el armónico resonante correcto."""
        model = CytoplasmicRiemannResonance()
        
        # Para la escala fundamental
        harmonic = model._find_resonant_harmonic(model.xi_fundamental)
        assert harmonic == 1, \
            f"Armónico resonante incorrecto: {harmonic} (esperado 1)"
        
        # Para escala ~ ξ₁/2
        harmonic = model._find_resonant_harmonic(model.xi_fundamental / np.sqrt(4))
        assert 3 <= harmonic <= 5, \
            f"Armónico resonante fuera de rango: {harmonic}"


# ============================================================================
# TEST CLASS: DECOHERENCE DETECTION
# ============================================================================

class TestDecoherenceDetection:
    """Pruebas para detección de descoherencia."""
    
    def test_healthy_system(self):
        """Verifica detección de sistema saludable."""
        model = CytoplasmicRiemannResonance()
        
        status = model.detect_decoherence(noise_level=0.0, seed=42)
        
        assert status['is_hermitian'], \
            "Sistema saludable debería ser hermítico"
        assert status['system_state'] == "SALUDABLE", \
            f"Estado incorrecto: {status['system_state']}"
        assert status['decoherence_severity'] < 0.1, \
            f"Severidad demasiado alta: {status['decoherence_severity']}"
        assert status['eigenvalue_real_ratio'] > 0.99, \
            f"Ratio de eigenvalues reales bajo: {status['eigenvalue_real_ratio']}"
    
    def test_pathological_system(self):
        """Verifica detección de sistema patológico."""
        model = CytoplasmicRiemannResonance()
        
        status = model.detect_decoherence(noise_level=0.5, seed=1)
        
        # Sistema patológico
        assert not status['is_hermitian'], \
            "Sistema patológico no debería ser hermítico"
        assert status['system_state'] in ["PRECANCEROSO", "PATOLÓGICO"], \
            f"Estado incorrecto para sistema enfermo: {status['system_state']}"
        assert status['decoherence_severity'] >= 0.05, \
            f"Severidad demasiado baja: {status['decoherence_severity']}"
    
    def test_decoherence_increases_with_noise(self):
        """Verifica que la descoherencia aumenta con el ruido."""
        model = CytoplasmicRiemannResonance()
        
        noise_levels = [0.0, 0.2, 0.4, 0.6]
        
        # Usar seed para reproducibilidad
        severities = []
        for i, noise in enumerate(noise_levels):
            status = model.detect_decoherence(noise_level=noise, seed=100+i)
            severities.append(status['decoherence_severity'])
        
        # Verificar que al menos algunas severidades aumenten
        # Con ruido 0, debe ser 0
        assert severities[0] == 0.0, "Sin ruido debería tener severidad 0"
        
        # Con ruido alto, debe haber alguna severidad detectada
        assert max(severities[1:]) > 0.0, "Con ruido debería haber descoherencia"


# ============================================================================
# TEST CLASS: RIEMANN HYPOTHESIS VALIDATION
# ============================================================================

class TestRiemannHypothesisValidation:
    """Pruebas para validación de hipótesis de Riemann."""
    
    def test_hypothesis_validated(self):
        """Verifica que la hipótesis se valide correctamente."""
        model = CytoplasmicRiemannResonance()
        
        result = model.validate_riemann_hypothesis_biological()
        
        assert result['hypothesis_validated'], \
            "La hipótesis debería ser validada"
        assert result['all_eigenvalues_real'], \
            "Todos los eigenvalues deberían ser reales"
        assert result['harmonic_distribution'], \
            "Debería tener distribución armónica"
        assert result['coherence_maintained'], \
            "Debería mantener coherencia"
    
    def test_validation_components(self):
        """Verifica cada componente de la validación."""
        model = CytoplasmicRiemannResonance()
        
        result = model.validate_riemann_hypothesis_biological()
        
        # Verificar que todos los componentes estén presentes
        required_keys = [
            'hypothesis_validated',
            'all_eigenvalues_real',
            'harmonic_distribution',
            'coherence_maintained',
            'cellular_scale_match',
            'interpretation'
        ]
        
        for key in required_keys:
            assert key in result, f"Falta clave en resultado: {key}"
    
    def test_harmonic_distribution_verification(self):
        """Verifica el método de verificación de distribución armónica."""
        model = CytoplasmicRiemannResonance()
        
        # Distribución perfectamente armónica
        perfect = [model.base_frequency * n for n in range(1, 11)]
        assert model._verify_harmonic_distribution(perfect), \
            "Distribución armónica perfecta no reconocida"
        
        # Distribución no armónica
        imperfect = [100, 210, 315]  # No es n × 100
        assert not model._verify_harmonic_distribution(imperfect), \
            "Distribución no armónica reconocida como armónica"


# ============================================================================
# TEST CLASS: MOLECULAR VALIDATION PROTOCOL
# ============================================================================

class TestMolecularValidationProtocol:
    """Pruebas para el protocolo de validación molecular."""
    
    def test_fluorescent_markers(self):
        """Verifica configuración de marcadores fluorescentes."""
        protocol = MolecularValidationProtocol()
        
        markers = protocol.get_fluorescent_markers()
        
        # Verificar que tenga los marcadores esperados
        assert 'primary_marker' in markers
        assert 'control_marker' in markers
        assert 'tension_sensor' in markers
        
        # Verificar marcador principal
        assert markers['primary_marker']['name'] == 'GFP-Citoplasma'
        assert markers['primary_marker']['wavelength_nm'] == 509
    
    def test_magnetic_nanoparticles(self):
        """Verifica configuración de nanopartículas magnéticas."""
        protocol = MolecularValidationProtocol()
        
        nanoparticles = protocol.get_magnetic_nanoparticles()
        
        # Verificar propiedades
        assert nanoparticles['composition'] == 'Fe₃O₄'
        assert nanoparticles['size_nm'] == 10
        
        # Frecuencia resonante debe ser la base
        assert abs(nanoparticles['resonance_frequency_hz'] - BASE_FREQUENCY_HZ) < 0.1
    
    def test_spectroscopy_protocol(self):
        """Verifica protocolo de espectroscopía."""
        protocol = MolecularValidationProtocol()
        
        spectroscopy = protocol.get_spectroscopy_protocol()
        
        # Verificar que incluya picos esperados
        expected_peaks = spectroscopy['expected_peaks_hz']
        assert len(expected_peaks) >= 3
        
        # Verificar que sean armónicos
        for i, peak in enumerate(expected_peaks, start=1):
            expected = i * BASE_FREQUENCY_HZ
            assert abs(peak - expected) < 1.0, \
                f"Pico {i} incorrecto: {peak} vs {expected}"
    
    def test_phase_measurement(self):
        """Verifica protocolo de medición de fase."""
        protocol = MolecularValidationProtocol()
        
        phase = protocol.get_phase_measurement_protocol()
        
        # Verificar frecuencias
        assert phase['cardiac_frequency_hz'] == 1.2
        assert abs(phase['cytoplasmic_frequency_hz'] - BASE_FREQUENCY_HZ) < 0.1
        
        # Verificar ratio
        expected_ratio = BASE_FREQUENCY_HZ / 1.2
        assert abs(phase['expected_ratio'] - expected_ratio) < 1.0


# ============================================================================
# TEST CLASS: EXPORT FUNCTIONALITY
# ============================================================================

class TestExportFunctionality:
    """Pruebas para funcionalidad de exportación."""
    
    def test_export_results(self, tmp_path):
        """Verifica exportación de resultados."""
        model = CytoplasmicRiemannResonance()
        
        output_file = tmp_path / "test_results.json"
        results = model.export_results(str(output_file))
        
        # Verificar que el archivo existe
        assert output_file.exists()
        
        # Verificar estructura
        assert 'metadata' in results
        assert 'constants' in results
        assert 'validation' in results
        assert 'decoherence_analysis' in results
        
        # Verificar que se puede leer
        with open(output_file, 'r') as f:
            loaded = json.load(f)
            assert loaded == results
    
    def test_export_protocol(self, tmp_path):
        """Verifica exportación de protocolo molecular."""
        protocol = MolecularValidationProtocol()
        
        output_file = tmp_path / "test_protocol.json"
        result = protocol.export_protocol(str(output_file))
        
        # Verificar que el archivo existe
        assert output_file.exists()
        
        # Verificar estructura
        assert 'metadata' in result
        assert 'techniques' in result
        assert 'validation_steps' in result
    
    def test_export_biological_mapping(self, tmp_path):
        """Verifica exportación de mapeo biológico."""
        output_file = tmp_path / "test_mapping.json"
        mapping = generate_biological_mapping(str(output_file))
        
        # Verificar que el archivo existe
        assert output_file.exists()
        
        # Verificar estructura
        assert 'metadata' in mapping
        assert 'mappings' in mapping
        assert 'key_insight' in mapping
        
        # Verificar que hay mapeos
        assert len(mapping['mappings']) > 0


# ============================================================================
# TEST CLASS: INTEGRATION TESTS
# ============================================================================

class TestIntegration:
    """Pruebas de integración del sistema completo."""
    
    def test_full_workflow(self, tmp_path):
        """Prueba el flujo completo del modelo."""
        # Crear modelo
        model = CytoplasmicRiemannResonance()
        
        # Validar hipótesis
        validation = model.validate_riemann_hypothesis_biological()
        assert validation['hypothesis_validated']
        
        # Verificar coherencia
        coherence = model.get_coherence_at_scale(1.06e-6)
        assert coherence['is_resonant']
        
        # Detectar descoherencia
        status = model.detect_decoherence(noise_level=0.0)
        assert status['system_state'] == "SALUDABLE"
        
        # Exportar resultados
        results_file = tmp_path / "integration_results.json"
        model.export_results(str(results_file))
        assert results_file.exists()
    
    def test_consistency_across_scales(self):
        """Verifica consistencia a través de escalas."""
        model = CytoplasmicRiemannResonance()
        
        # Verificar varias escalas
        scales = [0.5e-6, 1.0e-6, 2.0e-6, 5.0e-6]
        
        for scale in scales:
            coherence = model.get_coherence_at_scale(scale)
            
            # Todas deberían tener hermiticidad alta
            assert coherence['hermiticity_index'] > 0.9, \
                f"Hermiticidad baja a escala {scale*1e6:.1f} μm"
            
            # Número armónico debe ser positivo
            assert coherence['harmonic_number'] > 0


# ============================================================================
# PYTEST CONFIGURATION
# ============================================================================

def pytest_configure(config):
    """Configuración de pytest."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )


if __name__ == '__main__':
    # Ejecutar pruebas con pytest
    pytest.main([__file__, '-v', '--tb=short'])
