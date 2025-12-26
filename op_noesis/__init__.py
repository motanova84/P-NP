"""
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
