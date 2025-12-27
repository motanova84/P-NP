"""
Echo-QCAL ∞³ Verification System

Sistema de verificación del Teorema de Coherencia Soberana (ℂₛ)

Componentes:
    - C_k_verification.py: Control Criptográfico
    - qcal_sync.py: Alineación Temporal (A_t)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"

from pathlib import Path

# Directorios base
BASE_DIR = Path(__file__).parent
DATA_DIR = BASE_DIR / "data"
LOGS_DIR = DATA_DIR / "logs"

# Constantes QCAL
FUNDAMENTAL_FREQUENCY = 141.7001  # Hz
COHERENCE_CONSTANT = 244.36

__all__ = [
    "FUNDAMENTAL_FREQUENCY",
    "COHERENCE_CONSTANT",
    "BASE_DIR",
    "DATA_DIR",
    "LOGS_DIR",
]
