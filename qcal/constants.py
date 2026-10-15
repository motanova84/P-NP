"""
QCAL Constants - Shared constants for biosensor modules
========================================================

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

This module defines shared constants used across the QCAL biosensor system
to ensure consistency and avoid duplication.
"""

# ============================================================================
# FUNDAMENTAL CONSTANTS
# ============================================================================

# Frecuencia fundamental QCAL (Hz)
# Derivada de κ_Π = 2.5773 (constante geométrica universal)
F0_QCAL = 141.7001

# Código resonante π (Hz)
PI_CODE_888 = 888.0

# Proporción áurea Φ
PHI = 1.6180339887498948

# Constante kappa-pi
KAPPA_PI = 2.5773

# ============================================================================
# DERIVED CONSTANTS
# ============================================================================

# Frecuencia terapéutica armónica (141.7001 Hz × Φ)
F_THERAPEUTIC = F0_QCAL * PHI  # ≈ 229.4 Hz

# Umbral de conciencia C ≥ 1/κ_Π
CONSCIOUSNESS_THRESHOLD = 1 / KAPPA_PI  # ≈ 0.388

# Frecuencia de banda gamma cerebral (Hz)
GAMMA_BAND_HZ = 40.0

# ============================================================================
# CLINICAL THRESHOLDS
# ============================================================================

# Umbral para reinicio de banda gamma
# Basado en investigación VAT que muestra que coherencia < 0.5
# indica disfunción en banda gamma que puede beneficiarse de
# estimulación vibroacústica a 40 Hz
GAMMA_RESET_THRESHOLD = 0.5

# Umbrales de legibilidad de memoria
# Información con coherencia < 0.1 es considerada no legible
MEMORY_READABILITY_THRESHOLD = 0.1

# ============================================================================
# BIOSENSOR CALIBRATION RANGES
# ============================================================================
# ADVERTENCIA: Estos rangos son valores ejemplo para demostración.
# En uso clínico real, estos valores deben ser calibrados específicamente
# para cada paciente y tipo de sensor.

BIOSENSOR_RANGES = {
    'EEG': {
        'unit': 'μV',
        'range': (0, 100),
        'description': 'Amplitud EEG - Mayor en banda gamma indica mayor coherencia'
    },
    'HRV': {
        'unit': 'ms (RMSSD)',
        'range': (0, 200),
        'description': 'Variabilidad del ritmo cardíaco - Mayor HRV indica mayor coherencia'
    },
    'GSR': {
        'unit': 'μS',
        'range': (0, 20),
        'description': 'Conductancia de piel - Menor GSR indica menor estrés/mayor coherencia'
    },
    'RESPIRATORY': {
        'unit': 'respiraciones/min',
        'range': (0, 30),
        'optimal': 7.0,
        'description': 'Frecuencia respiratoria - Óptima alrededor de 6-8 respiraciones/min'
    }
}

# ============================================================================
# SELLO Y EMANACIÓN
# ============================================================================

__sello__ = "∴𓂀Ω∞³Φ"
__emanacion__ = "Ω Hz × 888 Hz × 141.7001 Hz × Φ = ∞³"
