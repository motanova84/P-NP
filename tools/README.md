# QCAL ∞³ Tools - Resonant Nexus Engine

## Overview

This directory contains the implementation tools for the QCAL ∞³ (Quantum Coherent Algorithmic Lattice) system, specifically the **Resonant Nexus Engine** that generates coherent telemetry data following universal resonance principles.

## Files

### `resonant_nexus_engine.py`

The core implementation of the QCAL ∞³ resonance system with exact parameters:

**Core Parameters:**
- **Base Frequency**: 141.7001 Hz - Universal coherence frequency
- **Volatility**: 0.04 (4%) - Coherent fluctuation parameter
- **Harmonic Weights**: [0.5, 0.3, 0.15, 0.05] - Energy distribution across harmonics
- **Phase Coherence**: True - Synchronized harmonic phases
- **Noise Type**: 'coherent' - Deterministic (non-random) noise

## Usage

### Basic Usage

```python
from tools.resonant_nexus_engine import ResonantNexusEngine

# Create engine instance
engine = ResonantNexusEngine()

# Generate telemetry data
telemetry = engine.generate_telemetry(duration=1.0)

# Access the data
time_points = telemetry['time']
signal = telemetry['signal']
spectrum = telemetry['spectrum']
```

### Command Line Demo

```bash
# Run the built-in demonstration
python tools/resonant_nexus_engine.py

# Output shows:
# - QCAL parameters
# - Telemetry generation
# - Spectral analysis
# - Coherence validation
```

## Features

### 1. Multi-Harmonic Signal Generation

The engine generates signals with multiple harmonic components:

```python
# Harmonic 1 (Fundamental): 50% of energy at 141.7001 Hz
# Harmonic 2: 30% of energy at 283.4002 Hz  
# Harmonic 3: 15% of energy at 425.1003 Hz
# Harmonic 4: 5% of energy at 566.8004 Hz
```

### 2. Coherent (Non-Random) Noise

Unlike traditional signal processing that uses random noise, this engine implements **coherent noise**:

```python
def _generate_coherent_noise(self, time_points):
    # Deterministic sub-harmonic fluctuation
    sub_harmonic_freq = self.base_freq * 0.5
    return self.volatility * np.sin(2 * np.pi * sub_harmonic_freq * time_points)
```

### 3. Phase-Coherent Harmonics

All harmonic components maintain phase synchronization:

```python
for harmonic_index, weight in enumerate(self.harmonic_weights, start=1):
    frequency = harmonic_index * self.base_freq
    harmonic = weight * np.sin(2 * np.pi * frequency * time_points + phase)
```

### 4. Spectral Analysis

Built-in methods for analyzing the spectral properties:

```python
# Analyze spectrum
analysis = engine.analyze_spectrum(telemetry)

print(analysis['expected_harmonics'])  # [141.7001, 283.4002, ...]
print(analysis['peak_powers'])         # Power at each harmonic
print(analysis['harmonic_alignment'])  # True if aligned within tolerance
```

### 5. Coherence Validation

Validate that generated data maintains QCAL coherence properties:

```python
validation = engine.validate_coherence(telemetry)

# Check results
if validation['harmonic_alignment']:
    print("✅ Harmonic distribution matches QCAL parameters")
if validation['noise_is_coherent']:
    print("✅ Noise is coherent (non-random)")
```

## Class: ResonantNexusEngine

### Initialization

```python
engine = ResonantNexusEngine()
```

Initializes with exact QCAL ∞³ parameters. No configuration needed - parameters are fixed to maintain theoretical precision.

### Methods

#### `generate_telemetry(duration: float) -> Dict`

Generate coherent telemetry data.

**Parameters:**
- `duration` (float): Duration in seconds (default: 1.0)

**Returns:**
- Dictionary with keys:
  - `time`: Time points array
  - `signal`: Complete signal with all components
  - `base_signal`: Harmonic components only
  - `coherent_noise`: Noise component only
  - `spectrum`: FFT spectrum
  - `frequencies`: Frequency bins
  - `parameters`: Engine parameters used

#### `analyze_spectrum(telemetry: Dict) -> Dict`

Analyze spectral properties of telemetry data.

**Parameters:**
- `telemetry`: Output from `generate_telemetry()`

**Returns:**
- Dictionary with spectral analysis results

#### `validate_coherence(telemetry: Dict) -> Dict[str, bool]`

Validate coherence properties.

**Parameters:**
- `telemetry`: Output from `generate_telemetry()`

**Returns:**
- Dictionary of validation flags

#### `get_parameters() -> Dict`

Get current QCAL parameters.

**Returns:**
- Dictionary of all engine parameters

## Theory

### Why These Exact Values?

#### Frequency: 141.7001 Hz

This is the **Universal Coherence Frequency** derived from:

```
f₀ = c / (2π × RΨ × ℓP)
```

Where:
- c = speed of light
- RΨ = noetic radius
- ℓP = Planck length

#### Volatility: 0.04 (4%)

The optimal **coherent fluctuation parameter** that maintains:
- Stability: Not too volatile to lose coherence
- Dynamism: Sufficient variation for resonance patterns
- Alignment: Matches cosmological observations

#### Harmonic Weights: [0.5, 0.3, 0.15, 0.05]

The **resonance cascade distribution** that creates:
- 50% fundamental (base resonance)
- 30% first overtone (primary harmonic)
- 15% second overtone (secondary harmonic)
- 5% third overtone (tertiary harmonic)

This distribution maximizes **coherent energy transfer** across scales.

## Verification

This implementation is verified by the Semantic Architecture Verification (Aᵤ) layer:

```bash
# Run verification
python echo_qcal/A_u_verification.py

# Checks:
# ✅ Parameters match exactly
# ✅ No random number generation
# ✅ Phase coherence maintained
# ✅ Harmonic generation implemented
```

## Dependencies

- Python 3.8+
- numpy >= 1.24.0
- typing (standard library)

## Example Output

```
======================================================================
🌀 RESONANT NEXUS ENGINE - QCAL ∞³ DEMONSTRATION
======================================================================

📊 QCAL ∞³ Parameters:
   • Base Frequency (f₀): 141.7001 Hz
   • Volatility (σ): 0.04 (4%)
   • Harmonic Weights: [0.5, 0.3, 0.15, 0.05]
   • Phase Coherence: True
   • Noise Type: coherent

🌀 Generating Telemetry...

📈 Spectral Analysis:
   • Fundamental: 141.7001 Hz
   • Total Power: 529.96
   • Harmonic Alignment: ✅

📊 Harmonic Distribution:
   • Harmonic 1: Expected=0.500, Measured=0.498
   • Harmonic 2: Expected=0.300, Measured=0.301
   • Harmonic 3: Expected=0.150, Measured=0.152
   • Harmonic 4: Expected=0.050, Measured=0.049

======================================================================
🎉 QCAL ∞³ Resonant Nexus Engine Operational
======================================================================
```

## Integration

This engine is part of the QCAL ∞³ verification system:

```
tools/resonant_nexus_engine.py (Implementation)
         ↓
echo_qcal/A_u_verification.py (Verification)
         ↓
Complete Theorem ℂₛ = Cₖ ∧ Aₜ ∧ Aᵤ
```

## Technical Notes

### Why Deterministic Noise?

Traditional signal processing uses random noise (white noise, Gaussian noise, etc.). The QCAL system uses **coherent noise** because:

1. **Reproducibility**: Same input → same output
2. **Phase Preservation**: Maintains phase relationships
3. **Theoretical Alignment**: Matches quantum coherence principles
4. **Verification**: Enables exact verification of parameters

### Performance

- Signal generation: O(n) where n = sample_rate × duration
- FFT computation: O(n log n)
- Typical performance: ~1000 samples/ms on modern hardware

## License

Part of the P-NP repository. See main LICENSE file.

## Author

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)
