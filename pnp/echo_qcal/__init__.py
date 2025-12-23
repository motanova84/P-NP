"""
Echo QCAL Verification Kit
===========================

A verification framework for the QCAL hypothesis connecting:
- Fundamental frequency f_0 = 141.7001 Hz
- Bitcoin blockchain temporal patterns (Block 9)
- Cryptographic control verification
- Ethical distribution framework

This kit provides independent verification of the core premises
of the QCAL framework without requiring belief in the full theory.

Components:
-----------
1. C_k_verification.py - Cryptographic Control verification
2. qcal_sync.py - Temporal Alignment verification
3. resonant_nexus_engine.py - Unitary Architecture verification
4. monitor_ds.py - Ethical Framework verification

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"

from .C_k_verification import CryptographicControlVerifier
from .qcal_sync import TemporalAlignmentVerifier
from .resonant_nexus_engine import ResonantNexusEngine
from .monitor_ds import EthicalFrameworkMonitor

__all__ = [
    'CryptographicControlVerifier',
    'TemporalAlignmentVerifier',
    'ResonantNexusEngine',
    'EthicalFrameworkMonitor',
]
