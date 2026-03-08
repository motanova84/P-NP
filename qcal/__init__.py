"""
QCAL Biosensor Module - Biomechanical Interface to the Emanant Principle
=========================================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

Este módulo implementa la primera interfaz biomecánica del principio emanante,
integrando memoria ARN volátil, biosensores y detección de desarmonías.
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo (JMMB Ψ✧)"

from .constants import __sello__, __emanacion__
from .rna_volatile_memory import RNAVolatileMemory
from .biosensor_hub import BiosensorHub
from .disharmony_detector import DisharmonyDetector
from .adn_riemann import CodificadorADNRiemann
from .p_np_solver_bridge import (
    resolver_p_vs_np_vibracional,
    encontrar_maxima_coherencia,
    certificar_logos
)

__all__ = [
    '__sello__',
    '__emanacion__',
    'RNAVolatileMemory',
    'BiosensorHub', 
    'DisharmonyDetector',
    'CodificadorADNRiemann',
    'resolver_p_vs_np_vibracional',
    'encontrar_maxima_coherencia',
    'certificar_logos'
]
