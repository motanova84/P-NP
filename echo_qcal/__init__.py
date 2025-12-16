"""
Echo QCAL: Simulación y Análisis de Coherencia Temporal

Módulos para la simulación de propagación de coherencia
y filtrado entrópico de datos en el marco QCAL.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
License: MIT
"""

from .propagation_model import PropagationModel, CoherenceEvent
from .entropic_filter import EntropicFilter, FilterResult

__all__ = [
    "PropagationModel",
    "CoherenceEvent",
    "EntropicFilter",
    "FilterResult"
]

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo · JMMB Ψ✧ ∞³"
