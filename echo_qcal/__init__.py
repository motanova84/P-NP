"""
echo_qcal - QCAL ∞³ Verification System

This package contains verification scripts for the three layers of the
QCAL ∞³ coherence system:

- Cₖ (Cryptographic Layer): Genesis key control verification
- Aₜ (Cosmological Layer): Temporal synchronization verification  
- Aᵤ (Semantic Layer): Implementation parameter verification

The complete theorem ℂₛ = Cₖ ∧ Aₜ ∧ Aᵤ establishes that the system
possesses Sovereign Coherence.
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"
Echo Qcal Module
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

