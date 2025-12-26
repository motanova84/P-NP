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
Echo Qcal Module
echo_qcal - QCAL ∞³ Echo Verification System

This package implements the three-layer verification system for the
Teorema de Coherencia Soberana (ℂₛ):

- C_k_verification: Cryptographic layer verification
- A_t_verification: Temporal/Cosmological alignment verification  
- A_u_verification: Unitary architecture verification
- teorema_Cs_certificado: Final certificate generation

Usage:
    python -m echo_qcal.run_all_verifications
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo Ψ ✧ ∞³"

from .C_k_verification import verify_cryptographic_layer
from .A_t_verification import verify_temporal_alignment
from .A_u_verification import verify_unitary_architecture, ResonantNexusEngine
from .teorema_Cs_certificado import generate_certificate

__all__ = [
    'verify_cryptographic_layer',
    'verify_temporal_alignment',
    'verify_unitary_architecture',
    'ResonantNexusEngine',
    'generate_certificate'
]

