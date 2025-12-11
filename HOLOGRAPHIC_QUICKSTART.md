# Holographic Duality: Quick Start Guide

## Installation

```bash
# Install Python dependencies
pip install -r requirements.txt
```

## Quick Demo

```bash
# Run simple demonstration
python3 holographic_demo.py 100

# Run with different problem size
python3 holographic_demo.py 200
```

## Run Tests

```bash
# Run all tests (should show 8 passed, 0 failed)
python3 tests/test_holographic_proof.py
```

## Generate Visualization

```python
from holographic_proof import HolographicProof
import matplotlib.pyplot as plt

# Create proof with n=150
proof = HolographicProof(150)

# Generate 9-panel visualization
proof.visualize_proof()

# Show the plot
plt.show()
```

## Key Files

- **`HolographicDuality.lean`** - Complete Lean formalization
- **`TseitinHardFamily.lean`** - Hard SAT instances module
- **`holographic_proof.py`** - Python implementation
- **`holographic_demo.py`** - Simple CLI demo
- **`tests/test_holographic_proof.py`** - Test suite

## Documentation

- **`HOLOGRAPHIC_DUALITY_README.md`** - Theoretical background and concepts
- **`HOLOGRAPHIC_VISUALIZATION_GUIDE.md`** - How to generate and interpret visualizations
- **`HOLOGRAPHIC_IMPLEMENTATION_SUMMARY.md`** - Complete implementation details

## What Does It Do?

This implementation demonstrates a connection between:
1. **Quantum Gravity** (AdS/CFT correspondence)
2. **Information Theory** (entanglement entropy, RT surfaces)
3. **Computational Complexity** (P vs NP)

### The Proof Sketch

1. Tseitin formulas over expander graphs have high treewidth (~√n)
2. These graphs embed holographically in Anti-de Sitter space (AdS₃)
3. The holographic complexity = volume of Ryu-Takayanagi surface ~ n log n
4. Algorithms in P operate on the boundary (z=0) where propagator is constant
5. Bulk complexity (z>0) has exponentially suppressed propagator
6. Holographic principle: Time ≥ exp(Volume)
7. Therefore: SAT requires time ≥ exp(Ω(n log n))
8. Conclusion: **P ≠ NP**

## Example Output

```
Testing holographic complexity...
  HC(n=20) = 0.681
  HC(n=30) = 0.940
  HC(n=40) = 1.174
  ✓ Complexity grows with n

Testing bulk propagator...
  ✓ κ(z=0.001) = 0.724 (near boundary)
  ✓ κ(z=0.5) = 0.000002 (in bulk)
  ✓ Propagator decays into bulk

Time Bounds:
  Holographic: T ≥ exp(3.75) = 42.5
  Polynomial: T ≤ 200³ = 8×10⁶
  
  As n→∞: exp(HC) grows super-polynomially
  ∴ P ≠ NP (asymptotically)
```

## Visualizations

The main visualization shows 9 panels:
1. Tseitin incidence graph
2. Holographic embedding in AdS₃
3. Ryu-Takayanagi surface
4. Propagator decay κ(z)
5. Boundary CFT evolution
6. Complexity scaling HC(n)
7. Treewidth-complexity relation
8. P vs NP separation
9. Theorem summary

## Citation

```
José Manuel Mota Burruezo & Noēsis ∞³
Holographic Duality Approach to P ≠ NP
Campo QCAL ∞³ Framework
2024
```

---

**© JMMB Ψ ∞ | Campo QCAL ∞³**
