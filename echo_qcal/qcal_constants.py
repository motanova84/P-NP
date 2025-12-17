"""
QCAL ∞³ Constants and Universal Parameters

This module defines the fundamental constants of the QCAL ∞³ framework
that govern the convergence between computational consciousness and
the Bitcoin blockchain.
"""

# ============================================================================
# QCAL ∞³ FUNDAMENTAL CONSTANTS
# ============================================================================

# Primordial frequency (Hz) - The universal pulse of coherence
F0 = 141.7001  # ± 0.0001 Hz

# Primordial period (seconds)
TAU0 = 1.0 / F0  # 0.00705715 s

# ============================================================================
# BITCOIN BLOCKCHAIN CONSTANTS
# ============================================================================

# Block 9 timestamp (2009-01-09 17:15:00 UTC)
T_BLOCK9 = 1231511700.000000  # Unix timestamp

# Block 0 (Genesis) signature metadata
GENESIS_ADDRESS = "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
GENESIS_MESSAGE = "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z"
GENESIS_SIGNATURE = "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldmBTNqPes3UfC7ZDuuuESPlEPlagjRI="

# ============================================================================
# STATISTICAL ANALYSIS PARAMETERS
# ============================================================================

# Temporal window for synchrony analysis (2 hours in seconds)
WINDOW = 7200  # Bitcoin 2009 constraint

# Coherence threshold (10 ms)
EPSILON = 0.01  # seconds

# ============================================================================
# HARMONIC WEIGHTS (Cognitive Distribution)
# ============================================================================

HARMONIC_WEIGHTS = {
    1: 0.50,  # f₀ (50%)
    2: 0.30,  # 2f₀ (30%)
    3: 0.15,  # 3f₀ (15%)
    4: 0.05,  # 4f₀ (5%)
}

# ============================================================================
# RESONANCE ENGINE PARAMETERS
# ============================================================================

# Base volatility (coherent, non-random)
SIGMA = 0.04  # 4% volatility

# Default simulation cycles
DEFAULT_CYCLES = 1000

# ============================================================================
# SOVEREIGN COHERENCE THRESHOLD
# ============================================================================

# Probability threshold for Sovereign Coherence
P_THRESHOLD = 1e-14  # 10^-14

# Coherence percentage threshold
COHERENCE_THRESHOLD = 0.999  # 99.9%

# ============================================================================
# UNIVERSAL CONSTANT (from Calabi-Yau geometry)
# ============================================================================

KAPPA_PI = 2.5773  # Universal invariant

# Consciousness quantization threshold
C_THRESHOLD = 1.0 / KAPPA_PI  # ≈ 0.388
