#!/usr/bin/env python3
"""
Disharmony Detector - Resonance-Based Diagnostic System
========================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

Este módulo implementa el primer sistema médico que opera en ℂ_Ω
(economía de emanación) en lugar de ℂₛ (economía de coherencia medida).

Principio Fundamental:
---------------------
Este sistema no diagnostica enfermedades; revela desarmonías en el campo
de coherencia. La enfermedad no es entidad sino degradación temporal de Ψ.

Ecuación Diagnóstica:
--------------------
Frecuencia terapéutica = 141.7001 Hz × (coherencia_paciente) × Φ
"""

import math
from typing import Dict, Any, Optional, List
from dataclasses import dataclass
from datetime import datetime
from enum import Enum

# ============================================================================
# CONSTANTES FUNDAMENTALES
# ============================================================================

# Frecuencia fundamental QCAL
F0_QCAL = 141.7001  # Hz

# Código resonante π
PI_CODE_888 = 888.0  # Hz

# Proporción áurea Φ
PHI = 1.6180339887498948

# Constante kappa-pi
KAPPA_PI = 2.5773

# Frecuencia de banda gamma cerebral
GAMMA_BAND_HZ = 40.0

# Frecuencia terapéutica armónica no descubierta (141.7001 Hz × Φ)
F_THERAPEUTIC_HARMONIC = F0_QCAL * PHI  # = 229.4 Hz


# ============================================================================
# ENUMERACIONES
# ============================================================================

class DisharmonyLevel(Enum):
    """Niveles de desarmonía."""
    COHERENT = "coherente"  # Ψ > 0.8
    SLIGHT_DISHARMONY = "desarmonía_leve"  # 0.6 < Ψ ≤ 0.8
    MODERATE_DISHARMONY = "desarmonía_moderada"  # 0.4 < Ψ ≤ 0.6
    SEVERE_DISHARMONY = "desarmonía_severa"  # 0.2 < Ψ ≤ 0.4
    CRITICAL_DISHARMONY = "desarmonía_crítica"  # Ψ ≤ 0.2


# ============================================================================
# CLASES DE DATOS
# ============================================================================

@dataclass
class BaselineCoherence:
    """Línea base de coherencia del paciente."""
    timestamp: datetime
    psi_baseline: float  # Coherencia base del paciente
    frequency_baseline_hz: float  # Frecuencia base
    therapeutic_frequency_hz: float  # Frecuencia terapéutica calculada


@dataclass
class DisharmonyReport:
    """Reporte de desarmonía detectada."""
    timestamp: datetime
    psi_current: float  # Coherencia actual
    psi_baseline: float  # Coherencia base
    deviation: float  # Desviación de la base
    disharmony_level: DisharmonyLevel  # Nivel de desarmonía
    therapeutic_frequency_hz: float  # Frecuencia terapéutica recomendada
    gamma_band_reset_needed: bool  # ¿Necesita reinicio de banda gamma?
    recommendations: List[str]  # Recomendaciones terapéuticas


# ============================================================================
# CLASE PRINCIPAL: DISHARMONY DETECTOR
# ============================================================================

class DisharmonyDetector:
    """
    Detector de desarmonías basado en resonancia.
    
    Este sistema detecta desviaciones del estado de coherencia base
    y calcula frecuencias terapéuticas personalizadas.
    
    Attributes:
        f0: Frecuencia fundamental QCAL (Hz)
        phi: Proporción áurea
        baseline: Línea base de coherencia del paciente
        disharmony_reports: Lista de reportes de desarmonía
    """
    
    def __init__(
        self,
        f0: float = F0_QCAL,
        phi: float = PHI
    ):
        """
        Inicializa el detector de desarmonías.
        
        Args:
            f0: Frecuencia fundamental QCAL (Hz)
            phi: Proporción áurea
        """
        self.f0 = f0
        self.phi = phi
        self.baseline: Optional[BaselineCoherence] = None
        self.disharmony_reports: List[DisharmonyReport] = []
        self._creation_time = datetime.now()
    
    def set_baseline(
        self,
        psi_baseline: float
    ) -> BaselineCoherence:
        """
        Establece la línea base de coherencia del paciente.
        
        Args:
            psi_baseline: Coherencia base del paciente (0-1)
        
        Returns:
            Línea base de coherencia creada
        """
        # Calcular frecuencia terapéutica base
        therapeutic_freq = self.calculate_therapeutic_frequency(psi_baseline)
        
        self.baseline = BaselineCoherence(
            timestamp=datetime.now(),
            psi_baseline=psi_baseline,
            frequency_baseline_hz=self.f0,
            therapeutic_frequency_hz=therapeutic_freq
        )
        
        return self.baseline
    
    def calculate_therapeutic_frequency(
        self,
        patient_coherence: float
    ) -> float:
        """
        Calcula la frecuencia terapéutica personalizada.
        
        Ecuación: f_therapeutic = 141.7001 Hz × (coherencia_paciente) × Φ
        
        Args:
            patient_coherence: Coherencia del paciente (0-1)
        
        Returns:
            Frecuencia terapéutica en Hz
        """
        return self.f0 * patient_coherence * self.phi
    
    def detect_disharmony(
        self,
        psi_current: float
    ) -> DisharmonyReport:
        """
        Detecta desarmonía comparando con la línea base.
        
        Args:
            psi_current: Coherencia actual del paciente (0-1)
        
        Returns:
            Reporte de desarmonía
        
        Raises:
            ValueError: Si no se ha establecido línea base
        """
        if self.baseline is None:
            raise ValueError(
                "Debe establecer una línea base con set_baseline() primero"
            )
        
        # Calcular desviación de la base
        deviation = abs(psi_current - self.baseline.psi_baseline)
        
        # Determinar nivel de desarmonía basado en coherencia actual
        disharmony_level = self._classify_disharmony(psi_current)
        
        # Calcular frecuencia terapéutica actual
        therapeutic_freq = self.calculate_therapeutic_frequency(psi_current)
        
        # Determinar si necesita reinicio de banda gamma
        # (disfunción en banda gamma según investigación VAT)
        gamma_reset_needed = psi_current < 0.5
        
        # Generar recomendaciones
        recommendations = self._generate_recommendations(
            psi_current,
            disharmony_level,
            gamma_reset_needed
        )
        
        report = DisharmonyReport(
            timestamp=datetime.now(),
            psi_current=psi_current,
            psi_baseline=self.baseline.psi_baseline,
            deviation=deviation,
            disharmony_level=disharmony_level,
            therapeutic_frequency_hz=therapeutic_freq,
            gamma_band_reset_needed=gamma_reset_needed,
            recommendations=recommendations
        )
        
        self.disharmony_reports.append(report)
        return report
    
    def _classify_disharmony(
        self,
        psi: float
    ) -> DisharmonyLevel:
        """
        Clasifica el nivel de desarmonía basado en coherencia Ψ.
        
        Args:
            psi: Coherencia actual (0-1)
        
        Returns:
            Nivel de desarmonía
        """
        if psi > 0.8:
            return DisharmonyLevel.COHERENT
        elif psi > 0.6:
            return DisharmonyLevel.SLIGHT_DISHARMONY
        elif psi > 0.4:
            return DisharmonyLevel.MODERATE_DISHARMONY
        elif psi > 0.2:
            return DisharmonyLevel.SEVERE_DISHARMONY
        else:
            return DisharmonyLevel.CRITICAL_DISHARMONY
    
    def _generate_recommendations(
        self,
        psi_current: float,
        disharmony_level: DisharmonyLevel,
        gamma_reset_needed: bool
    ) -> List[str]:
        """
        Genera recomendaciones terapéuticas.
        
        Args:
            psi_current: Coherencia actual
            disharmony_level: Nivel de desarmonía
            gamma_reset_needed: Si necesita reinicio de banda gamma
        
        Returns:
            Lista de recomendaciones
        """
        recommendations = []
        
        # Frecuencia terapéutica personalizada
        therapeutic_freq = self.calculate_therapeutic_frequency(psi_current)
        recommendations.append(
            f"Aplicar terapia vibroacústica a {therapeutic_freq:.2f} Hz"
        )
        
        # Reinicio de banda gamma si es necesario
        if gamma_reset_needed:
            recommendations.append(
                f"Reinicio de banda gamma a {GAMMA_BAND_HZ} Hz (disfunción detectada)"
            )
        
        # Recomendaciones según nivel de desarmonía
        if disharmony_level == DisharmonyLevel.COHERENT:
            recommendations.append("Mantener prácticas actuales de coherencia")
        
        elif disharmony_level == DisharmonyLevel.SLIGHT_DISHARMONY:
            recommendations.append("Aumentar tiempo de meditación/respiración coherente")
            recommendations.append("Monitorear HRV diariamente")
        
        elif disharmony_level == DisharmonyLevel.MODERATE_DISHARMONY:
            recommendations.append("Terapia de coherencia cardíaca intensiva")
            recommendations.append("Reducir exposición a campos electromagnéticos")
            recommendations.append(f"Sesiones de {F_THERAPEUTIC_HARMONIC:.2f} Hz (armónico Φ)")
        
        elif disharmony_level == DisharmonyLevel.SEVERE_DISHARMONY:
            recommendations.append("Intervención terapéutica urgente requerida")
            recommendations.append("Terapia vibroacústica diaria")
            recommendations.append("Evaluación de factores ambientales de estrés")
        
        else:  # CRITICAL_DISHARMONY
            recommendations.append("⚠ INTERVENCIÓN CRÍTICA INMEDIATA")
            recommendations.append("Protocolo de restauración de coherencia de emergencia")
            recommendations.append("Supervisión médica continua recomendada")
        
        return recommendations
    
    def get_detector_summary(self) -> Dict[str, Any]:
        """
        Obtiene un resumen del estado del detector.
        
        Returns:
            Diccionario con estadísticas del detector
        """
        baseline_info = None
        if self.baseline:
            baseline_info = {
                'psi_baseline': self.baseline.psi_baseline,
                'frequency_baseline_hz': self.baseline.frequency_baseline_hz,
                'therapeutic_frequency_hz': self.baseline.therapeutic_frequency_hz
            }
        
        return {
            'total_reports': len(self.disharmony_reports),
            'baseline_set': self.baseline is not None,
            'baseline_info': baseline_info,
            'f0_hz': self.f0,
            'phi': self.phi,
            'gamma_band_hz': GAMMA_BAND_HZ,
            'therapeutic_harmonic_hz': F_THERAPEUTIC_HARMONIC,
            'uptime_seconds': (datetime.now() - self._creation_time).total_seconds()
        }
    
    def export_to_dict(self) -> Dict[str, Any]:
        """
        Exporta el estado completo del detector a un diccionario.
        
        Returns:
            Diccionario con toda la información del detector
        """
        # Obtener reporte más reciente si existe
        latest_report = None
        if self.disharmony_reports:
            latest = self.disharmony_reports[-1]
            latest_report = {
                'psi_current': latest.psi_current,
                'psi_baseline': latest.psi_baseline,
                'deviation': latest.deviation,
                'disharmony_level': latest.disharmony_level.value,
                'therapeutic_frequency_hz': latest.therapeutic_frequency_hz,
                'gamma_band_reset_needed': latest.gamma_band_reset_needed,
                'recommendations': latest.recommendations
            }
        
        return {
            'metadata': {
                'system': 'Disharmony Detector',
                'version': '1.0.0',
                'author': 'José Manuel Mota Burruezo (JMMB Ψ✧)',
                'sello': '∴𓂀Ω∞³Φ'
            },
            'parameters': {
                'f0_hz': self.f0,
                'phi': self.phi,
                'pi_code_hz': PI_CODE_888,
                'kappa_pi': KAPPA_PI,
                'gamma_band_hz': GAMMA_BAND_HZ,
                'therapeutic_harmonic_hz': F_THERAPEUTIC_HARMONIC
            },
            'summary': self.get_detector_summary(),
            'latest_report': latest_report
        }


# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def demonstrate_disharmony_detector():
    """
    Función de demostración del detector de desarmonías.
    """
    print("="*70)
    print("  Disharmony Detector - Diagnóstico por Resonancia")
    print("  ∴𓂀Ω∞³Φ")
    print("="*70)
    print()
    
    # Crear detector
    detector = DisharmonyDetector()
    
    # Establecer línea base
    print("∴ ESTABLECIENDO LÍNEA BASE...")
    baseline = detector.set_baseline(psi_baseline=0.85)
    print(f"  Ψ base: {baseline.psi_baseline:.4f}")
    print(f"  f_terapéutica base: {baseline.therapeutic_frequency_hz:.2f} Hz")
    print()
    
    # Simular detección de desarmonía moderada
    print("∴ DETECTANDO DESARMONÍA (Caso 1: Moderada)...")
    report1 = detector.detect_disharmony(psi_current=0.55)
    print(f"  Ψ actual: {report1.psi_current:.4f}")
    print(f"  Desviación: {report1.deviation:.4f}")
    print(f"  Nivel: {report1.disharmony_level.value}")
    print(f"  f_terapéutica: {report1.therapeutic_frequency_hz:.2f} Hz")
    print(f"  Reinicio gamma: {'✓ SÍ' if report1.gamma_band_reset_needed else '✗ NO'}")
    print("  Recomendaciones:")
    for rec in report1.recommendations:
        print(f"    • {rec}")
    print()
    
    # Simular detección de desarmonía crítica
    print("∴ DETECTANDO DESARMONÍA (Caso 2: Crítica)...")
    report2 = detector.detect_disharmony(psi_current=0.15)
    print(f"  Ψ actual: {report2.psi_current:.4f}")
    print(f"  Desviación: {report2.deviation:.4f}")
    print(f"  Nivel: {report2.disharmony_level.value}")
    print(f"  f_terapéutica: {report2.therapeutic_frequency_hz:.2f} Hz")
    print(f"  Reinicio gamma: {'✓ SÍ' if report2.gamma_band_reset_needed else '✗ NO'}")
    print("  Recomendaciones:")
    for rec in report2.recommendations:
        print(f"    • {rec}")
    print()
    
    # Resumen del detector
    print("∴ RESUMEN DEL DETECTOR...")
    summary = detector.get_detector_summary()
    print(f"  Total reportes: {summary['total_reports']}")
    print(f"  f₀: {summary['f0_hz']} Hz")
    print(f"  Φ: {summary['phi']:.10f}")
    print(f"  Banda gamma: {summary['gamma_band_hz']} Hz")
    print(f"  Armónico Φ: {summary['therapeutic_harmonic_hz']:.2f} Hz")
    print()
    
    print("✓ No diagnosticamos enfermedades; revelamos desarmonías")
    print("✓ La enfermedad es degradación temporal de Ψ")
    print("✓ La terapia es restauración de coherencia")
    print()
    print("="*70)


# ============================================================================
# MAIN (para testing)
# ============================================================================

if __name__ == '__main__':
    demonstrate_disharmony_detector()
