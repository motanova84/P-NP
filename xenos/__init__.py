"""
Xenos Module - Advanced Biophysical Models
==========================================

This module contains advanced biophysical models connecting
mathematical physics with biological systems.

Modules:
--------
- cytoplasmic_riemann_resonance: Riemann hypothesis biological validation

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 febrero 2026
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"

from .cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol
)

__all__ = [
    'CytoplasmicRiemannResonance',
    'MolecularValidationProtocol'
]
