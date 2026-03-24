"""
Xenos Module - Advanced Biophysical Models
==========================================

This module contains advanced biophysical models connecting
mathematical physics with biological systems.

Modules:
--------
- cytoplasmic_riemann_resonance: Riemann hypothesis biological validation
- rna_riemann_wave: RNA-Riemann wave transducer system
- bio_resonance: Biological-quantum correlation validator

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 12 febrero 2026
Sello: ∴𓂀Ω∞³
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"

from .cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol
)

from .rna_riemann_wave import (
    RNARiemannWave,
    CodonSignature,
    demonstrate_aaa_correlation
)

from .bio_resonance import (
    BioResonanceValidator,
    ExperimentalResult,
    ValidationReport,
    demonstrate_bio_validation
)

__all__ = [
    'CytoplasmicRiemannResonance',
    'MolecularValidationProtocol',
    'RNARiemannWave',
    'CodonSignature',
    'demonstrate_aaa_correlation',
    'BioResonanceValidator',
    'ExperimentalResult',
    'ValidationReport',
    'demonstrate_bio_validation'
]
