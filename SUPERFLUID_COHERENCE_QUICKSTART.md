# SUPERFLUID COHERENCE - QUICK START GUIDE

## 🚀 Quick Start (3 commands)

```bash
# Run comprehensive demonstration
python examples/demo_superfluid_vortex.py

# Run all tests (58 tests, should be 100% passing)
python -m pytest tests/test_superfluid_coherence.py tests/test_vortex_quantum_bridge.py -v

# View individual module demonstrations
python src/superfluid_coherence.py
python src/vortex_quantum_bridge.py
```

## 📚 Core Concepts

### Coherence Parameter Ψ

The coherence parameter Ψ determines the computational regime:

| Regime | Ψ Range | Viscosity | Complexity | Description |
|--------|---------|-----------|------------|-------------|
| **NP Chaos** | Ψ < 0.88 | η ≈ 1.0 | Exponential | Turbulent information dispersal |
| **Transition** | 0.88 ≤ Ψ < 0.99 | 0 < η < 1 | Mixed | Phase transition in progress |
| **P Superfluid** | Ψ ≥ 0.99 | η → 0 | Polynomial | Coherent single-layer flow |

### Key Formulas

**Coherence Calculation**:
```python
Ψ = exp(-E/kT) * (1 - η_noise) * (1 + quantum_factor)
```

**Superfluid Fraction**:
```python
f_s = 1.0                                          # if Ψ ≥ 0.99
f_s = [(Ψ - 0.88) / (0.99 - 0.88)]^0.67            # if 0.88 < Ψ < 0.99
f_s = 0.0                                          # if Ψ < 0.88
```

**Viscosity**:
```python
η = η_0 * (1 - f_s)
```

**Quantum Jump Probability**:
```python
P(r) = 0.8463 * exp(-2.5773 * (r/r_core)²)
```

## 💻 Usage Examples

### Example 1: Detect Complexity Collapse

```python
from src.superfluid_coherence import SuperfluidCoherence

# Initialize detector
sc = SuperfluidCoherence(f0=141.7001)

# System evolution from chaos to superfluid
energies = [10.0, 5.0, 1.0, 0.1, 0.01]
temperatures = [2.0, 1.5, 1.0, 0.5, 0.3]
noise_levels = [0.5, 0.3, 0.1, 0.05, 0.001]

# Analyze collapse
analysis = sc.analyze_complexity_collapse(energies, temperatures, noise_levels)

# Print results
print(sc.generate_coherence_report(analysis))

# Check if collapse detected
if analysis['collapse_detected']:
    print(f"✅ P regime achieved in {analysis['p_superfluid_count']} states")
    print(f"   Superfluid indices: {analysis['superfluid_indices']}")
```

### Example 2: Quantum Wormhole Transport

```python
from src.vortex_quantum_bridge import VortexQuantumBridge

# Initialize 34-node quantum bridge
bridge = VortexQuantumBridge(f0=141.7001, num_nodes=34)

# Connect nodes (requires Ψ ≥ 0.95)
connected = bridge.connect_nodes(coherence_threshold=0.95)
print(f"Connected {connected} nodes to vortex bridge")

# Execute quantum transport
result = bridge.execute_quantum_transport(source=0, target=33)

if result['success']:
    print(f"✅ Quantum jump successful!")
    print(f"   Probability: {result['probability']:.2%}")
    print(f"   Coherence: {result['coherence']:.4f}")
else:
    print(f"❌ Quantum jump failed")
    print(f"   Reason: {result.get('reason', 'Unknown')}")
```

### Example 3: Calculate Wormhole Metrics

```python
from src.vortex_quantum_bridge import VortexQuantumBridge

bridge = VortexQuantumBridge()

# Compute metrics at core (r=0)
metrics = bridge.compute_wormhole_metrics(r=0.0, coherence=0.99)

print(f"Core Singularity Metrics:")
print(f"  g_rr: {metrics.g_rr} (infinite curvature)")
print(f"  Jump probability: {metrics.jump_probability:.2%}")
print(f"  Stability: {metrics.stability:.2%}")
print(f"  Curvature: {'∞' if np.isinf(metrics.curvature) else metrics.curvature}")
```

### Example 4: Detect Phase Transitions

```python
from src.superfluid_coherence import SuperfluidCoherence
import numpy as np

sc = SuperfluidCoherence()

# Time series of coherence values
coherences = np.linspace(0.5, 1.0, 100).tolist()

# Detect transitions
result = sc.detect_phase_transition(coherences)

print(f"Phase Transitions Detected: {result['transition_count']}")
print(f"Critical (NP→P) Transitions: {result['critical_count']}")

if result['has_collapse']:
    print("✅ Critical collapse detected!")
    for transition in result['critical_transitions']:
        print(f"  Step {transition['index']}: {transition['transition_type']}")
```

## 🔬 Testing

### Run All Tests
```bash
python -m pytest tests/test_superfluid_coherence.py tests/test_vortex_quantum_bridge.py -v
```

### Run Specific Test Class
```bash
# Test coherence calculations
python -m pytest tests/test_superfluid_coherence.py::TestCoherenceCalculation -v

# Test quantum transport
python -m pytest tests/test_vortex_quantum_bridge.py::TestQuantumTransport -v
```

### Expected Results
```
Superfluid Coherence: 24/24 tests passing ✅
Vortex Quantum Bridge: 34/34 tests passing ✅
Total: 58/58 tests passing (100% success rate)
```

## 📊 Interpreting Results

### Coherence Analysis Report

```
SUPERFLUID COHERENCE ANALYSIS REPORT
======================================================================

Mean Coherence (Ψ): 0.850000
Superfluid States:  15 / 100
Collapse Fraction:  15.00%

REGIME DISTRIBUTION:
  • NP Chaos (Ψ < 0.88):         60
  • Transition (0.88 ≤ Ψ < 0.99): 25
  • P Superfluid (Ψ ≥ 0.99):     15

✅ COMPLEXITY COLLAPSE DETECTED
   The system has achieved P regime (superfluid coherence).
   NP complexity has reduced to P simplicity.
```

**Interpretation**:
- **Mean Coherence**: Average Ψ across all states
- **Superfluid States**: Number of states with Ψ ≥ 0.99
- **Collapse Fraction**: Percentage of states in P regime
- **Distribution**: Breakdown by regime

### Wormhole Metrics

```
WORMHOLE METRICS:
  g_rr:             0.000000 (infinite curvature at core)
  Jump probability: 84.63%
  Stability:        99.00%
  Curvature:        ∞ (singularity)
```

**Interpretation**:
- **g_rr = 0**: Indicates wormhole throat (singularity)
- **Jump probability**: Quantum tunneling success rate
- **Stability > 90%**: Wormhole is stable for transport
- **Infinite curvature**: Confirms singularity presence

## 🎯 Common Use Cases

### Use Case 1: Monitor System Coherence
Track coherence evolution in a quantum system and detect when it transitions from NP to P complexity.

### Use Case 2: Quantum Communication
Use vortex bridge for inter-node quantum transport with high success probability.

### Use Case 3: Viscosity Analysis
Calculate effective viscosity to determine if system is in turbulent or superfluid state.

### Use Case 4: Phase Transition Prediction
Identify critical points where system will undergo NP→P phase transition.

## 🔧 Configuration

### Coherence Detector Configuration
```python
sc = SuperfluidCoherence(
    f0=141.7001  # Fundamental frequency (Hz)
)

# Thresholds (fixed):
sc.psi_chaos_threshold = 0.88      # NP chaos threshold
sc.psi_superfluid_threshold = 0.99  # P superfluid threshold
sc.kappa_pi = 2.5773302292          # Universal constant
```

### Vortex Bridge Configuration
```python
bridge = VortexQuantumBridge(
    f0=141.7001,                    # Fundamental frequency
    num_nodes=34,                   # Transport network size
    vortex_type=VortexType.SINGULAR # Vortex type
)

# Physical parameters:
bridge.r_core = 1.0                 # Core radius
bridge.gamma = 1.0                  # Circulation strength
bridge.core_probability = 0.8463    # 84.63% at core
```

## 📖 Documentation

- **Full Theory**: `TENSORES_FLUJO_DIMENSIONAL.md`
- **Implementation Summary**: `SUPERFLUID_COHERENCE_IMPLEMENTATION_SUMMARY.md`
- **API Documentation**: Docstrings in source files

## 🌟 Key Constants

```python
f₀ = 141.7001 Hz        # Fundamental coherence frequency
κ_π = 2.5773302292      # Universal Calabi-Yau constant
Ψ_c = 0.88              # Critical coherence (NP threshold)
Ψ_s = 0.99              # Superfluid coherence (P threshold)
P_core = 0.8463         # Core jump probability (84.63%)
```

## ⚠️ Important Notes

1. **Random Seeding**: Quantum transport includes randomness. Set `np.random.seed()` for reproducibility.
2. **Node Connection**: Not all nodes may connect depending on their initial coherence.
3. **Visualization**: Requires matplotlib. Demo will skip visualization if not available.
4. **Test Timing**: Some tests use random values; occasional variance is expected but should not affect pass/fail.

## 🆘 Troubleshooting

**Problem**: No nodes connect to vortex bridge  
**Solution**: Lower coherence threshold or increase node coherence in initialization

**Problem**: No critical transitions detected  
**Solution**: Ensure coherence values span from < 0.88 to ≥ 0.99

**Problem**: Tests fail with numerical precision errors  
**Solution**: Use `pytest.approx()` with appropriate tolerance

## 📞 Support

For issues or questions:
- Review: `SUPERFLUID_COHERENCE_IMPLEMENTATION_SUMMARY.md`
- Check: Tests in `tests/` directory
- Run: `examples/demo_superfluid_vortex.py` for working example

---

**∴ Presencia Eterna Confirmada ∴JMMB Ψ✧ ∴ HN-IA ∞³ ∴**
