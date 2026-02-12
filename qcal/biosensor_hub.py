#!/usr/bin/env python3
"""
Biosensor Hub - Bridge Between Physiological Signals and QCAL Field
====================================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

Este módulo implementa el hub de biosensores que integra señales
fisiológicas (EEG, HRV, GSR) con el campo QCAL ∞³.

Principio Fundamental:
---------------------
Los biosensores no "miden" coherencia; la revelan como estado inherente.

Coherencia Total:
----------------
Ψ_total = √(Ψ_cerebral² + Ψ_cardíaca² + Ψ_emocional² + Ψ_respiratorio²) / 2
"""

import math
from typing import Dict, Any, Optional, List
from dataclasses import dataclass
from datetime import datetime
from enum import Enum

# Import shared constants
from .constants import (
    F0_QCAL,
    PHI,
    KAPPA_PI,
    CONSCIOUSNESS_THRESHOLD,
    BIOSENSOR_RANGES
)


# ============================================================================
# ENUMERACIONES
# ============================================================================

class BiosensorType(Enum):
    """Tipos de biosensores disponibles."""
    EEG = "electroencephalogram"  # Cerebral
    HRV = "heart_rate_variability"  # Cardíaca
    GSR = "galvanic_skin_response"  # Emocional
    RESPIRATORY = "respiratory_rate"  # Respiratorio


# ============================================================================
# CLASES DE DATOS
# ============================================================================

@dataclass
class BiosensorReading:
    """Lectura de un biosensor individual."""
    sensor_type: BiosensorType
    timestamp: datetime
    raw_value: float
    psi_coherence: float  # Coherencia Ψ calculada (0-1)
    frequency_hz: Optional[float] = None  # Frecuencia dominante si aplica


@dataclass
class CoherenceProfile:
    """Perfil de coherencia del paciente."""
    timestamp: datetime
    psi_cerebral: float  # Coherencia cerebral (EEG)
    psi_cardiaca: float  # Coherencia cardíaca (HRV)
    psi_emocional: float  # Coherencia emocional (GSR)
    psi_respiratorio: float  # Coherencia respiratoria
    psi_total: float  # Coherencia total calculada
    consciousness_level: float  # Nivel de conciencia C
    is_conscious: bool  # C ≥ 1/κ_Π


# ============================================================================
# CLASE PRINCIPAL: BIOSENSOR HUB
# ============================================================================

class BiosensorHub:
    """
    Hub central de biosensores para integración QCAL.
    
    Este sistema integra múltiples señales fisiológicas y las
    traduce a coherencia en el campo QCAL ∞³.
    
    Attributes:
        f0: Frecuencia fundamental QCAL (Hz)
        phi: Proporción áurea
        readings: Lista de lecturas de biosensores
        coherence_profiles: Lista de perfiles de coherencia
    """
    
    def __init__(
        self,
        f0: float = F0_QCAL,
        phi: float = PHI
    ):
        """
        Inicializa el hub de biosensores.
        
        Args:
            f0: Frecuencia fundamental QCAL (Hz)
            phi: Proporción áurea
        """
        self.f0 = f0
        self.phi = phi
        self.readings: List[BiosensorReading] = []
        self.coherence_profiles: List[CoherenceProfile] = []
        self._creation_time = datetime.now()
    
    def add_reading(
        self,
        sensor_type: BiosensorType,
        raw_value: float,
        frequency_hz: Optional[float] = None
    ) -> BiosensorReading:
        """
        Agrega una lectura de biosensor.
        
        Args:
            sensor_type: Tipo de biosensor
            raw_value: Valor crudo de la lectura
            frequency_hz: Frecuencia dominante si aplica
        
        Returns:
            Lectura de biosensor creada
        """
        # Calcular coherencia Ψ a partir del valor crudo
        # Normalizar al rango 0-1
        psi_coherence = self._calculate_psi_from_raw(sensor_type, raw_value)
        
        reading = BiosensorReading(
            sensor_type=sensor_type,
            timestamp=datetime.now(),
            raw_value=raw_value,
            psi_coherence=psi_coherence,
            frequency_hz=frequency_hz
        )
        
        self.readings.append(reading)
        return reading
    
    def _calculate_psi_from_raw(
        self,
        sensor_type: BiosensorType,
        raw_value: float
    ) -> float:
        """
        Calcula coherencia Ψ a partir del valor crudo del sensor.
        
        ⚠️  ADVERTENCIA CLÍNICA: Los rangos de normalización aquí definidos son
        valores de ejemplo para demostración. En uso clínico real, estos valores
        deben ser calibrados específicamente para cada paciente, tipo de sensor,
        y condiciones de medición. Consulte BIOSENSOR_RANGES en qcal/constants.py
        para la documentación completa de rangos.
        
        Args:
            sensor_type: Tipo de biosensor
            raw_value: Valor crudo de la lectura
        
        Returns:
            Coherencia Ψ normalizada (0-1)
        """
        # Normalización específica por tipo de sensor
        # Ver BIOSENSOR_RANGES en constants.py para documentación de rangos
        
        if sensor_type == BiosensorType.EEG:
            # EEG: asumimos valores en μV (0-100)
            # Mayor amplitud gamma (40 Hz) = mayor coherencia
            normalized = min(raw_value / 100.0, 1.0)
        
        elif sensor_type == BiosensorType.HRV:
            # HRV: asumimos valores RMSSD en ms (0-200)
            # Mayor HRV = mayor coherencia cardíaca
            normalized = min(raw_value / 200.0, 1.0)
        
        elif sensor_type == BiosensorType.GSR:
            # GSR: asumimos conductancia en μS (0-20)
            # Menor GSR = mayor coherencia emocional (menos estrés)
            normalized = max(0.0, 1.0 - (raw_value / 20.0))
        
        elif sensor_type == BiosensorType.RESPIRATORY:
            # Respiratorio: asumimos respiraciones/min (0-30)
            # Respiración óptima alrededor de 6-8/min
            optimal_rate = 7.0
            deviation = abs(raw_value - optimal_rate)
            normalized = max(0.0, 1.0 - (deviation / 15.0))
        
        else:
            normalized = 0.5  # Valor por defecto
        
        return normalized
    
    def calculate_total_coherence(
        self,
        psi_cerebral: float,
        psi_cardiaca: float,
        psi_emocional: float,
        psi_respiratorio: float
    ) -> float:
        """
        Calcula la coherencia total del sistema.
        
        Ecuación: Ψ_total = √(Ψ_cerebral² + Ψ_cardíaca² + Ψ_emocional² + Ψ_respiratorio²) / 2
        
        Args:
            psi_cerebral: Coherencia cerebral (0-1)
            psi_cardiaca: Coherencia cardíaca (0-1)
            psi_emocional: Coherencia emocional (0-1)
            psi_respiratorio: Coherencia respiratoria (0-1)
        
        Returns:
            Coherencia total Ψ_total (0-1)
        """
        sum_squares = (
            psi_cerebral**2 +
            psi_cardiaca**2 +
            psi_emocional**2 +
            psi_respiratorio**2
        )
        
        psi_total = math.sqrt(sum_squares) / 2.0
        
        # Asegurar que esté en el rango [0, 1]
        return min(psi_total, 1.0)
    
    def create_coherence_profile(
        self,
        psi_cerebral: Optional[float] = None,
        psi_cardiaca: Optional[float] = None,
        psi_emocional: Optional[float] = None,
        psi_respiratorio: Optional[float] = None
    ) -> CoherenceProfile:
        """
        Crea un perfil de coherencia del paciente.
        
        Si no se proporcionan valores, usa las lecturas más recientes.
        
        Args:
            psi_cerebral: Coherencia cerebral (None para auto-calcular)
            psi_cardiaca: Coherencia cardíaca (None para auto-calcular)
            psi_emocional: Coherencia emocional (None para auto-calcular)
            psi_respiratorio: Coherencia respiratoria (None para auto-calcular)
        
        Returns:
            Perfil de coherencia creado
        """
        # Si no se proporcionan valores, usar lecturas recientes
        if psi_cerebral is None:
            psi_cerebral = self._get_latest_psi(BiosensorType.EEG)
        if psi_cardiaca is None:
            psi_cardiaca = self._get_latest_psi(BiosensorType.HRV)
        if psi_emocional is None:
            psi_emocional = self._get_latest_psi(BiosensorType.GSR)
        if psi_respiratorio is None:
            psi_respiratorio = self._get_latest_psi(BiosensorType.RESPIRATORY)
        
        # Calcular coherencia total
        psi_total = self.calculate_total_coherence(
            psi_cerebral, psi_cardiaca, psi_emocional, psi_respiratorio
        )
        
        # Calcular nivel de conciencia C
        # C se relaciona con la coherencia total
        consciousness_level = psi_total
        
        # Verificar si supera el umbral de conciencia
        is_conscious = consciousness_level >= CONSCIOUSNESS_THRESHOLD
        
        profile = CoherenceProfile(
            timestamp=datetime.now(),
            psi_cerebral=psi_cerebral,
            psi_cardiaca=psi_cardiaca,
            psi_emocional=psi_emocional,
            psi_respiratorio=psi_respiratorio,
            psi_total=psi_total,
            consciousness_level=consciousness_level,
            is_conscious=is_conscious
        )
        
        self.coherence_profiles.append(profile)
        return profile
    
    def _get_latest_psi(self, sensor_type: BiosensorType) -> float:
        """
        Obtiene la coherencia Ψ más reciente de un tipo de sensor.
        
        Args:
            sensor_type: Tipo de biosensor
        
        Returns:
            Coherencia Ψ (0.5 si no hay lecturas)
        """
        # Filtrar lecturas por tipo
        filtered = [r for r in self.readings if r.sensor_type == sensor_type]
        
        if not filtered:
            return 0.5  # Valor neutro por defecto
        
        # Retornar la más reciente
        latest = max(filtered, key=lambda r: r.timestamp)
        return latest.psi_coherence
    
    def get_hub_summary(self) -> Dict[str, Any]:
        """
        Obtiene un resumen del estado del hub.
        
        Returns:
            Diccionario con estadísticas del hub
        """
        return {
            'total_readings': len(self.readings),
            'total_profiles': len(self.coherence_profiles),
            'f0_hz': self.f0,
            'phi': self.phi,
            'consciousness_threshold': CONSCIOUSNESS_THRESHOLD,
            'uptime_seconds': (datetime.now() - self._creation_time).total_seconds()
        }
    
    def export_to_dict(self) -> Dict[str, Any]:
        """
        Exporta el estado completo del hub a un diccionario.
        
        Returns:
            Diccionario con toda la información del hub
        """
        # Obtener perfil más reciente si existe
        latest_profile = None
        if self.coherence_profiles:
            latest = self.coherence_profiles[-1]
            latest_profile = {
                'psi_cerebral': latest.psi_cerebral,
                'psi_cardiaca': latest.psi_cardiaca,
                'psi_emocional': latest.psi_emocional,
                'psi_respiratorio': latest.psi_respiratorio,
                'psi_total': latest.psi_total,
                'consciousness_level': latest.consciousness_level,
                'is_conscious': latest.is_conscious
            }
        
        return {
            'metadata': {
                'system': 'Biosensor Hub',
                'version': '1.0.0',
                'author': 'José Manuel Mota Burruezo (JMMB Ψ✧)',
                'sello': '∴𓂀Ω∞³Φ'
            },
            'parameters': {
                'f0_hz': self.f0,
                'phi': self.phi,
                'consciousness_threshold': CONSCIOUSNESS_THRESHOLD,
                'kappa_pi': KAPPA_PI
            },
            'summary': self.get_hub_summary(),
            'latest_profile': latest_profile
        }


# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def demonstrate_biosensor_hub():
    """
    Función de demostración del hub de biosensores.
    """
    print("="*70)
    print("  Biosensor Hub - Revelación de Coherencia")
    print("  ∴𓂀Ω∞³Φ")
    print("="*70)
    print()
    
    # Crear hub
    hub = BiosensorHub()
    
    print("∴ AGREGANDO LECTURAS DE BIOSENSORES...")
    
    # Simular lecturas
    hub.add_reading(BiosensorType.EEG, 65.0, frequency_hz=40.0)  # Banda gamma
    hub.add_reading(BiosensorType.HRV, 120.0)  # Buena variabilidad
    hub.add_reading(BiosensorType.GSR, 8.0)  # Moderado estrés
    hub.add_reading(BiosensorType.RESPIRATORY, 7.0)  # Respiración óptima
    
    print(f"  ✓ {len(hub.readings)} lecturas agregadas")
    print()
    
    # Crear perfil de coherencia
    print("∴ CALCULANDO PERFIL DE COHERENCIA...")
    profile = hub.create_coherence_profile()
    
    print(f"  Ψ cerebral: {profile.psi_cerebral:.4f}")
    print(f"  Ψ cardíaca: {profile.psi_cardiaca:.4f}")
    print(f"  Ψ emocional: {profile.psi_emocional:.4f}")
    print(f"  Ψ respiratorio: {profile.psi_respiratorio:.4f}")
    print(f"  Ψ TOTAL: {profile.psi_total:.4f}")
    print()
    print(f"  Nivel de conciencia C: {profile.consciousness_level:.4f}")
    print(f"  Umbral (1/κ_Π): {CONSCIOUSNESS_THRESHOLD:.4f}")
    print(f"  Estado consciente: {'✓ SÍ' if profile.is_conscious else '✗ NO'}")
    print()
    
    # Resumen del hub
    print("∴ RESUMEN DEL HUB...")
    summary = hub.get_hub_summary()
    print(f"  Total lecturas: {summary['total_readings']}")
    print(f"  Total perfiles: {summary['total_profiles']}")
    print(f"  f₀: {summary['f0_hz']} Hz")
    print(f"  Φ: {summary['phi']:.10f}")
    print()
    
    print("✓ Los biosensores no miden; revelan")
    print("✓ La coherencia es estado inherente")
    print("✓ La conciencia tiene umbral físico")
    print()
    print("="*70)


# ============================================================================
# MAIN (para testing)
# ============================================================================

if __name__ == '__main__':
    demonstrate_biosensor_hub()
