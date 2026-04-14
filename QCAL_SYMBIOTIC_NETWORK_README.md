# QCAL Symbiotic Network - Documentation

## 🌐 Overview

The QCAL Symbiotic Network is a coherence mapping system that enables AI assistants (like GitHub Copilot) to understand and navigate the interconnected ecosystem of mathematical repositories in the motanova84 organization. This system creates a "noetic field" that links multiple repositories through shared constants, protocols, and mathematical frameworks.

## 📁 Core Components

### 1. Configuration Files

#### `coherence_map.json`
The "compass" file that defines the QCAL ∞³ Symbiotic Network structure:

```json
{
  "system": "QCAL ∞³ Symbiotic Network",
  "version": "1.0.0",
  "frequency": "141.7001 Hz",
  "axioms": {
    "emission": "Constitutional base of πCODE economy",
    "sovereignty": "88 Sovereign NFTs (Pulsars)",
    "resonance": "888 Hz Pulse Synchronization"
  },
  "nodes": [...]
}
```

**Purpose**: Defines the network topology and core axioms that govern the symbiotic relationships between repositories.

#### `CORE_SYMBIO.json`
The portal file that provides identity nodes and constants:

```json
{
  "protocol": "QCAL-SYMBIO-BRIDGE",
  "origin": "motanova84",
  "identity_nodes": {
    "ledger": "economia-qcal-nodo-semilla",
    "spectral": "141hz",
    "verification": "Ramsey",
    ...
  },
  "constants": {
    "f0": 141.7001,
    "limit_nfts": 88,
    "resonance": 888,
    "r66": 108
  }
}
```

**Purpose**: Maps functional roles to repositories and provides universal constants.

### 2. Python Scripts

#### `crear_faro_noetico.py`
Creates a `.qcal_symbiosis.md` file in the current repository that marks it as part of the QCAL ecosystem.

**Usage**:
```bash
python3 crear_faro_noetico.py
```

**Output**: Creates `.qcal_symbiosis.md` with repository links and context.

#### `link_ecosystem.py`
The main "Rastreo de Gracia" (Grace Tracking) script that:
1. Updates the main `.qcal_beacon` file
2. Creates `.qcal_symbiosis.md` with cross-repository links
3. Generates beacon files in subdirectories

**Usage**:
```bash
python3 link_ecosystem.py
```

**Output**:
- Updated `.qcal_beacon` in repository root
- `.qcal_symbiosis.md` with ecosystem links
- `.qcal_beacon` files in subdirectories (core/, src/, etc.)

### 3. Math Library

#### `qcal_math_core.py`
Main entry point for the unified QCAL mathematical library.

**Features**:
- `QCALMathLibrary` class with universal constants
- Mathematical functions for the RAM protocol (Ramsey-Adelic-Mathematics)
- Convenience wrapper functions

**Example Usage**:
```python
from qcal_math_core import QCALMathLibrary

# Access constants
print(QCALMathLibrary.CONSTANTS["FREQ_GW"])  # 141.7001

# Calculate Shapiro delay
delay = QCALMathLibrary.shapiro_delay(mass=1.0, distance=10.0)

# Calculate Ramsey vibration
vibration = QCALMathLibrary.ramsey_vibration(n=5)

# Get frequency resonance
freq = QCALMathLibrary.frequency_resonance(harmonic=3)  # 425.1003 Hz

# Calculate coherence factor
factor = QCALMathLibrary.coherence_factor(100)

# Get pulsar fraction
frac = QCALMathLibrary.pulsar_fraction(44)  # 0.5 (44/88)
```

#### `core/math/qcal_lib.py`
Modular version of the math library that can be imported as:

```python
from core.math import QCALMathLibrary
```

## 🔑 Key Concepts

### The RAM Protocol (Ramsey-Adelic-Mathematics)

The RAM protocol integrates:
- **R(6,6) = 108**: Ramsey number resolution from motanova84/Ramsey
- **f₀ = 141.7001 Hz**: Universal frequency from GW250114 analysis
- **88 Pulsars**: Sovereign NFT limit (MAX_PULSARS constant)
- **Ψ = 0.999999**: Perfect coherence factor

### Network Nodes

The QCAL ecosystem consists of seven interconnected repositories:

1. **economia-qcal-nodo-semilla**: Genesis / Ledger
2. **Ramsey**: Verification / R(6,6)
3. **Riemann-adelic**: Spectral Proof / Zeta Connection
4. **141hz**: Universal Constant / GW Analysis
5. **P-NP**: Complexity Resolution (this repository)
6. **3D-Navier-Stokes**: Fluid Dynamics / Turbulence
7. **adelic-bsd**: Arithmetic Compatibility

## 📊 Directory Structure

```
P-NP/
├── coherence_map.json          # Network topology definition
├── CORE_SYMBIO.json            # Identity nodes and constants
├── .qcal_beacon                # Main beacon (auto-generated)
├── .qcal_symbiosis.md          # Symbiosis links (auto-generated)
├── crear_faro_noetico.py       # Simple beacon creator
├── link_ecosystem.py           # Full ecosystem linker
├── qcal_math_core.py          # Main math library
└── core/
    ├── __init__.py
    └── math/
        ├── __init__.py
        ├── qcal_lib.py         # Modular math library
        └── .qcal_beacon        # Subdirectory beacon
```

## 🚀 Quick Start

### 1. Initialize the QCAL Ecosystem

```bash
# Run the ecosystem linker
python3 link_ecosystem.py
```

This will:
- Update `.qcal_beacon` with current network state
- Create `.qcal_symbiosis.md` with repository cross-references
- Generate beacon files in subdirectories

### 2. Use the Math Library

```python
# Import the library
from qcal_math_core import QCALMathLibrary

# Access universal constants
constants = QCALMathLibrary.CONSTANTS
print(f"Frequency: {constants['FREQ_GW']} Hz")
print(f"Ramsey R(6,6): {constants['RAMSEY_R66']}")
print(f"Max Pulsars: {constants['MAX_PULSARS']}")

# Perform calculations
shapiro = QCALMathLibrary.shapiro_delay(1.0, 10.0)
ramsey = QCALMathLibrary.ramsey_vibration(5)
```

### 3. Create a Beacon in Your Directory

```bash
python3 crear_faro_noetico.py
```

## 🧪 Testing

Run the comprehensive test suite:

```bash
python3 test_qcal_symbiotic_network.py
```

Tests cover:
- JSON file structure and validation
- Math library functions and constants
- Script imports and functionality
- Beacon file generation
- Cross-repository consistency

## 🔧 Advanced Usage

### Custom Beacon Creation

You can create custom beacons programmatically:

```python
import link_ecosystem

# Load configuration
coherence = link_ecosystem.load_coherence_map()
symbio = link_ecosystem.load_core_symbio()

# Create main beacon
link_ecosystem.crear_faro_principal()

# Create symbiosis file
link_ecosystem.crear_faro_symbiosis()

# Create subdirectory beacons
link_ecosystem.crear_faros_subdirectorios()
```

### Extending the Math Library

Add new functions to `qcal_math_core.py` or `core/math/qcal_lib.py`:

```python
@staticmethod
def new_function(param):
    """Your new mathematical function"""
    return param * QCALMathLibrary.CONSTANTS["PSI"]
```

## 🌟 Integration with GitHub Copilot

The QCAL Symbiotic Network is designed to help GitHub Copilot:

1. **Understand Context**: The `.qcal_symbiosis.md` file provides explicit links to related repositories
2. **Access Constants**: Universal constants are centralized in `QCALMathLibrary.CONSTANTS`
3. **Navigate the Ecosystem**: Beacon files mark important directories
4. **Maintain Coherence**: The coherence map ensures consistent terminology across repositories

## 📖 Related Repositories

- [motanova84/Riemann-adelic](https://github.com/motanova84/-jmmotaburr-riemann-adelic) - Quantum Geometry
- [motanova84/Ramsey](https://github.com/motanova84/Ramsey) - SAT Verification
- [motanova84/economia-qcal-nodo-semilla](https://github.com/motanova84/economia-qcal-nodo-semilla) - πCODE Economy
- [motanova84/141hz](https://github.com/motanova84/analisis-gw250114-141hz) - GW250114 Analysis

## 📝 Notes

- `.qcal_symbiosis.md` is auto-generated and excluded from git (via `.gitignore`)
- Beacon files are automatically created in: `core/`, `core/math/`, `src/`, `echo_qcal/`, `formal/`
- The system is frequency-based: all operations resonate at 141.7001 Hz
- Maximum coherence (Ψ = 0.999999) is maintained across all calculations

## 🔄 Updating the Network

When adding new repositories or constants:

1. Update `coherence_map.json` with new nodes
2. Update `CORE_SYMBIO.json` with new constants or identity nodes
3. Run `python3 link_ecosystem.py` to regenerate beacons
4. Test with `python3 test_qcal_symbiotic_network.py`

---

**Version**: 1.0.0  
**Frequency**: 141.7001 Hz  
**Protocol**: QCAL-SYMBIO-BRIDGE  
**Origin**: motanova84
