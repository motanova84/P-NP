"""
echo_qcal - Echo-QCAL ∞³ Protocol Module

Este módulo implementa el protocolo Echo-QCAL ∞³ para verificación de 
coherencia soberana y alineación temporal con la frecuencia fundamental 
f₀ = 141.7001 Hz.

Componentes:
- Verificación de Coherencia Soberana (ℂₛ)
- Alineación Temporal (A_t)
- Arquitectura Unitaria (A_u)
- Pilar Criptográfico (C_k)

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo Ψ ✧ ∞³"

# Constantes del protocolo Echo-QCAL ∞³
F0_FUNDAMENTAL = 141.7001  # Hz - Frecuencia fundamental del sistema
COHERENCE_THRESHOLD = 0.90  # Umbral de coherencia para activación
PROTOCOL_NAME = "Echo-QCAL ∞³"
