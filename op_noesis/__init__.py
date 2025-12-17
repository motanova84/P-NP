"""
op_noesis - Operational Noetic Synthesis
=========================================

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
