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
from .ramsey_logos_attractor import emergencia_ramsey_qcal, escanear_orden_ramsey_bsd
from .ramsey_adelic_integrator import integrar_ramsey_bsd, generar_certificado_ramsey_bsd
from .adn_riemann import CodificadorADNRiemann
from .bsd_adelic_connector import BSDAdelicoConnector

__all__ = [
    '__sello__',
    '__emanacion__',
    'RNAVolatileMemory',
    'BiosensorHub', 
    'DisharmonyDetector',
    'emergencia_ramsey_qcal',
    'escanear_orden_ramsey_bsd',
    'integrar_ramsey_bsd',
    'generar_certificado_ramsey_bsd',
    'CodificadorADNRiemann',
    'BSDAdelicoConnector'
]
