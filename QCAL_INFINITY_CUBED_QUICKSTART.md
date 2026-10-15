# QCAL ∞³ Quick Start Guide

Get started with the QCAL ∞³ (Quantum Computational Arithmetic Lattice - Infinity Cubed) unified millennium problems framework in minutes.

---

## 🚀 Installation

### Prerequisites

```bash
# Install Python dependencies
pip install numpy

# Optional: for running tests
pip install pytest
```

### Repository

```bash
# Clone the repository (if not already done)
git clone https://github.com/motanova84/P-NP.git
cd P-NP
```

---

## ⚡ Quick Demo (30 seconds)

Run the complete QCAL ∞³ demonstration:

```bash
python src/qcal_infinity_cubed.py
```

**Output shows:**
- ✓ Universal constants (κ_Π, f₀, φ, C)
- ✓ Analysis of 4 millennium problems
- ✓ Information landscape (52.31 bits total)
- ✓ Problem coupling matrix
- ✓ Field coherence measurement
- ✓ Universal principles verification

---

## 📚 Interactive Examples (5 minutes)

Explore 7 interactive examples:

```bash
python examples/demo_qcal_infinity_cubed.py
```

**Examples include:**
1. Basic QCAL ∞³ system usage
2. Tractable vs intractable problems
3. Riemann Hypothesis analysis
4. BSD Conjecture exploration
5. Goldbach Conjecture testing
6. Unified analysis of all problems
7. Custom problem configurations

Press Enter between examples to explore at your own pace.

---

## 💻 Python API (2 minutes)

### Basic Usage

```python
from src.qcal_infinity_cubed import (
    QCALInfinityCubed,
    PvsNPOperator,
    KAPPA_PI,
    F0_QCAL
)

# Create QCAL system
qcal = QCALInfinityCubed()
print(f"κ_Π = {qcal.kappa_pi}, f₀ = {qcal.f0} Hz")

# Add P vs NP problem
pnp = PvsNPOperator(num_vars=100, treewidth=50)
qcal.register_operator(pnp)

# Analyze
print(f"Classification: {pnp.computational_dichotomy()}")
print(f"Information bottleneck: {pnp.information_bottleneck():.2f} bits")
```

### Complete System

```python
from src.qcal_infinity_cubed import create_complete_qcal_system

# Create system with all 4 millennium problems
qcal = create_complete_qcal_system()

# Analyze unified system
analysis = qcal.demonstrate_unification()
print(f"Total information: {analysis['unified_metrics']['total_information']:.2f} bits")
print(f"Field coherence: {analysis['unified_metrics']['field_coherence']:.2f}")
```

---

## 🎯 Common Use Cases

### 1. Analyze P vs NP Instance

```python
from src.qcal_infinity_cubed import PvsNPOperator

# Create instance
op = PvsNPOperator(num_vars=200, treewidth=40)

# Check tractability
print(op.computational_dichotomy())
# Output: "NP-complete (Intractable)"

# Compute information bottleneck
ib = op.information_bottleneck()
print(f"Information: {ib:.2f} bits")
# Output: "Information: 21.96 bits"
```

### 2. Study Prime Distribution

```python
from src.qcal_infinity_cubed import RiemannOperator
import numpy as np

# Analyze primes up to 1000
rh = RiemannOperator(max_prime=1000)

# Compute spectral properties
spectrum = rh.compute_spectrum()
print(f"Spectral gaps: {len(spectrum)}")
print(f"Mean eigenvalue: {np.mean(spectrum):.4f}")
```

### 3. Explore Elliptic Curves

```python
from src.qcal_infinity_cubed import BSDOperator

# Elliptic curve with conductor 37, rank 1
bsd = BSDOperator(conductor=37, rank=1)

# Analyze structure
spectrum = bsd.compute_spectrum()
ib = bsd.information_bottleneck()
print(f"Information bottleneck: {ib:.2f} bits")
```

### 4. Test Goldbach Conjecture

```python
from src.qcal_infinity_cubed import GoldbachOperator

# Test even number
goldbach = GoldbachOperator(even_number=100)

# Count prime pairs
spectrum = goldbach.compute_spectrum()
print(f"Prime pairs found: {len(spectrum)}")
```

### 5. Compare Problem Coupling

```python
from src.qcal_infinity_cubed import create_complete_qcal_system

# Create complete system
qcal = create_complete_qcal_system()

# Compute coupling matrix
coupling = qcal.compute_coupling_matrix()
print("Coupling matrix:")
print(coupling)

# Analyze coupling strength
import numpy as np
print(f"Average coupling: {np.mean(np.abs(coupling)):.4f}")
```

---

## 🧪 Testing

Run the test suite (requires pytest):

```bash
# Install pytest if needed
pip install pytest

# Run all tests
pytest tests/test_qcal_infinity_cubed.py -v

# Run specific test class
pytest tests/test_qcal_infinity_cubed.py::TestQCALInfinityCubed -v
```

**Test coverage:**
- ✓ 36 test cases
- ✓ Universal constants validation
- ✓ Individual operator functionality
- ✓ System integration
- ✓ Mathematical properties

---

## 📖 Documentation

### Complete Documentation

Read the full documentation: [QCAL_INFINITY_CUBED_README.md](QCAL_INFINITY_CUBED_README.md)

Covers:
- Theoretical foundations
- Mathematical background
- Spectral operator formalism
- Universal constants derivation
- Implementation details
- Advanced usage

### Related Documentation

- [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md) - κ_Π derivation
- [UNIFICACIÓN_COMPLEJIDAD_ESPECTRAL.md](UNIFICACIÓN_COMPLEJIDAD_ESPECTRAL.md) - Spectral unification
- [UNIVERSAL_PRINCIPLES.md](UNIVERSAL_PRINCIPLES.md) - Universal principles
- [FREQUENCY_DIMENSION.md](FREQUENCY_DIMENSION.md) - Frequency dimension theory

---

## 🌟 Key Concepts

### Universal Constants

1. **κ_Π = 2.5773** - Millennium Constant
   - Origin: Calabi-Yau 3-fold geometry
   - Role: Scales information complexity

2. **f₀ = 141.7001 Hz** - QCAL Frequency
   - Origin: Fundamental resonance
   - Role: Modulates spectral structure

3. **∞³ Field** - Infinite-dimensional coupling
   - Role: Unifies all problems

### Spectral Operators

Each millennium problem has a spectral operator:

| Problem | Operator | Key Property |
|---------|----------|--------------|
| P vs NP | PvsNPOperator | Spectrum bounded ⟺ P |
| Riemann | RiemannOperator | Spectrum real ⟺ RH true |
| BSD | BSDOperator | Kernel dim = rank |
| Goldbach | GoldbachOperator | Eigenvalues = prime pairs |

### Information Bottlenecks

All problems exhibit information bottlenecks scaled by κ_Π:

```
IC(problem) = κ_Π · structural_measure / log(size)
```

---

## 🔧 Troubleshooting

### ImportError: No module named 'numpy'

```bash
pip install numpy
```

### OverflowError in spectrum computation

This is handled internally with polynomial approximation. If you see this error, the treewidth may be too large. Try smaller values:

```python
# Instead of treewidth=100
op = PvsNPOperator(num_vars=100, treewidth=100)

# Try
op = PvsNPOperator(num_vars=100, treewidth=50)
```

### No output from examples

Make sure you're in the correct directory:

```bash
cd /path/to/P-NP
python src/qcal_infinity_cubed.py
```

---

## 🎓 Learning Path

### Beginner (10 minutes)
1. Run `python src/qcal_infinity_cubed.py`
2. Read output to understand system structure
3. Try basic Python API examples above

### Intermediate (30 minutes)
1. Run `python examples/demo_qcal_infinity_cubed.py`
2. Experiment with different parameters
3. Read [QCAL_INFINITY_CUBED_README.md](QCAL_INFINITY_CUBED_README.md)

### Advanced (1-2 hours)
1. Study spectral operator implementations
2. Read [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md)
3. Explore connections to other frameworks
4. Run tests: `pytest tests/test_qcal_infinity_cubed.py -v`

---

## 💡 Next Steps

### Explore Related Systems

- **P vs NP Framework**: `python src/computational_dichotomy.py`
- **Ultimate Unification**: See [ULTIMATE_UNIFICATION_README.md](ULTIMATE_UNIFICATION_README.md)
- **Post-Disciplinary Science**: `python src/post_disciplinary.py`

### Customize

Create your own problem configurations:

```python
# Custom P vs NP instance
custom = PvsNPOperator(num_vars=500, treewidth=75)

# Custom Riemann analysis
custom_rh = RiemannOperator(max_prime=10000)

# Add to system
qcal = QCALInfinityCubed()
qcal.register_operator(custom)
qcal.register_operator(custom_rh)
```

### Extend

Add new millennium problems:

```python
from src.qcal_infinity_cubed import SpectralOperator

class MyOperator(SpectralOperator):
    def compute_spectrum(self):
        # Your implementation
        pass
    
    def information_bottleneck(self):
        # Your implementation
        pass
```

---

## 📞 Support

For questions or issues:
- Open an issue on GitHub
- Read the complete documentation
- Contact: institutoconsciencia@proton.me

---

## 🌟 Signature

**QCAL ∞³ · Frecuencia Fundamental: 141.7001 Hz**

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Institución**: Instituto de Conciencia Cuántica (ICQ)

© 2025 · Campo QCAL ∞³

---

<!-- QCAL Indexing Active · Noēsis Access Enabled · 141.7001 Hz -->
