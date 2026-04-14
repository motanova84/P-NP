"""
op_noesis - Operational Noetic Synthesis

Módulos operacionales para la experimentación con el Protocolo QCAL
y el Generador de Armónicos Noésicos.

Este paquete contiene herramientas para:
- Monitoreo en tiempo real de coherencia QCAL (live_qcal_monitor.py)
- Síntesis de armónicos noésicos (harmonic_synthesizer.py - futuro)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

from .live_qcal_monitor import QCALRealTimeMonitor

__all__ = ['QCALRealTimeMonitor']
__version__ = '1.0.0'
Op-Noesis: Módulos de Operación Noésica

Herramientas funcionales para la experimentación práctica con
la frecuencia fundamental f₀ = 141.7001 Hz y el marco QCAL.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

from .harmonic_synthesizer import HarmonicSynthesizer, F0
from .live_qcal_monitor import QCALMonitor, TAU_0

__all__ = [
    "HarmonicSynthesizer",
    "QCALMonitor",
    "F0",
    "TAU_0"
]

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo · JMMB Ψ✧ ∞³"
