# VIBRO-FLUORESCENCE QCAL QUICKSTART

## 🚀 Quick Start (3 Steps)

### 1. Install Dependencies
```bash
pip install numpy scipy pytest matplotlib
```

### 2. Run Tests
```bash
python -m pytest tests/test_vibro_fluorescence_qcal.py -v
```
**Expected**: 56/56 tests passing ✓

### 3. Run Demo
```bash
python examples/demo_vibro_fluorescence_qcal.py
```
**Output**: 6 visualization plots in `/tmp/`

---

## 📊 Key Equations

### Input Signal (Energy-Controlled)
```python
Ψ_input(t) = A₀[1 + m·sin(ωₚt)]·sin(ω₀t)
E_total = ∫|Ψ_input(t)|²dt = constant ∀ ωₚ
```

### QCAL Resonance
```python
ω_res = √(k_eff/m_eff) ≈ 2π × 141.7 Hz
```

### Fluorescence Response
```python
F(t) = F₀ + ΔF(ωₚ)·[1 + η·sin(ωₚt + φ(ωₚ))]
η(ωₚ) = ΔF(ωₚ) / (∂E/∂ωₚ)  # Critical QCAL parameter
```

### Falsification Criterion
```python
H₀: ΔF(ω) = constant ∀ ω
F_stat = [SS_between/df₁] / [SS_within/df₂]
Reject H₀ if F_stat > F_critical(α=0.001)
```

---

## 💻 Code Examples

### Example 1: Basic Coupling
```python
from src.vibro_fluorescence_qcal import VibroFluorescentCoupling

coupling = VibroFluorescentCoupling(mu=1.0, Q=0.1, chi2=0.01, chi3=0.001)
H = coupling.H_acoplamiento(E=1.0, grad_E=0.1)
print(f"Coupling energy: {H}")
```

### Example 2: Generate Input Signal
```python
from src.vibro_fluorescence_qcal import psi_input, energia_total
import numpy as np

t = np.linspace(0, 1, 10000)
dt = t[1] - t[0]
psi = psi_input(t, A0=1.0, m=0.5, omega_p=2.0, omega_0=141.7001)
E = energia_total(psi, dt)
print(f"Total energy: {E}")
```

### Example 3: Protein Oscillator
```python
from src.vibro_fluorescence_qcal import CoupledProteinOscillator
import numpy as np

osc = CoupledProteinOscillator(m=1.0, gamma=0.1, k=100.0, q=1.0)
omega = 2 * np.pi * 141.7
chi = osc.susceptibilidad(omega)
print(f"Susceptibility at QCAL frequency: {abs(chi):.4f}")
```

### Example 4: QCAL Predictions
```python
from src.vibro_fluorescence_qcal import prediccion_resonancia

pred = prediccion_resonancia(omega_p=141.7001, omega_0=141.7001)
print(f"Closest resonance: {pred['closest']}")
print(f"Distance: {pred['min_distance']:.6f}")
```

### Example 5: Experimental Protocol
```python
from src.vibro_fluorescence_qcal import ExperimentalProtocol
import numpy as np

protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=141.7001)
freq_range = np.linspace(1, 10, 50)
resultados = protocol.barrido_frecuencia(freq_range, duration=0.1, sample_rate=1000)

# Check energy conservation
energias = [resultados[f]["energy"] for f in freq_range]
print(f"Energy variation: {np.std(energias)/np.mean(energias)*100:.6f}%")
```

### Example 6: Statistical Falsification
```python
from src.vibro_fluorescence_qcal import hipotesis_nula_test
import numpy as np

F_resonante = np.random.normal(150, 5, 20)    # Enhanced at resonance
F_no_resonante = np.random.normal(100, 5, 20) # Normal elsewhere

result = hipotesis_nula_test(F_resonante, F_no_resonante)
print(f"F-statistic: {result['F_statistic']:.2f}")
print(f"p-value: {result['p_value']:.2e}")
print(f"Conclusion: {result['conclusion']}")
```

---

## 🎯 Constants

```python
OMEGA_0_QCAL = 141.7001      # Hz - QCAL carrier frequency
PSI_CRITICO = 0.888          # Critical coherence threshold
KAPPA_PI = 2.578208          # κ_Π constant
PHI = 1.618033988749         # Golden ratio
MAGICICADA_HARMONICS = [1, 2, 3, 13, 17]
```

---

## 📈 Experimental Workflow

```python
from src.vibro_fluorescence_qcal import ExperimentalProtocol
import numpy as np

# 1. Setup
protocol = ExperimentalProtocol(A0=1.0, m=0.5, omega_0=141.7001)

# 2. Frequency sweep (energy-controlled)
freq_range = np.linspace(0.1, 10, 100)
resultados = protocol.barrido_frecuencia(freq_range, duration=1.0, sample_rate=5000)

# 3. Measure fluorescence (replace with real measurements)
for freq in freq_range:
    signal = resultados[freq]["signal"]
    t = resultados[freq]["time"]
    medicion = protocol.medir_fluorescencia(signal, t, F0=100.0)
    resultados[freq]["F_mean"] = medicion["F_mean"]

# 4. QCAL analysis
analisis = protocol.analisis_qcal(resultados, sigma_threshold=2.0)

# 5. Decision
if analisis["confirmacion_qcal"]:
    print("✓ QCAL CONFIRMED")
    for res in analisis["resonancias_detectadas"]:
        print(f"  Resonance at {res['freq_medida']:.2f} Hz (harmonic {res['harmonic']})")
else:
    print("✗ QCAL NOT CONFIRMED")
```

---

## 🔬 Falsification Decision

### QCAL Hypothesis
> Response shows discrete spectral structure (peaks at specific frequencies) regardless of total energy

### Null Hypothesis (Traditional Biology)
> Response is flat across frequencies when energy is held constant

### Decision Rule
```python
# Calculate ratio at QCAL frequency vs control
ratio = ΔF(141.7 Hz) / ΔF(100 Hz)

if ratio > 1.5 with same energy:
    conclusion = "QCAL SUPPORTED"
elif ΔF(ω) ≈ constant ± experimental_error:
    conclusion = "QCAL FALSIFIED"
```

### Statistical Test
```python
result = hipotesis_nula_test(F_resonante, F_no_resonante, alpha=0.001)

if result["rechazar_H0"]:
    # F_stat > F_critical → significant difference
    conclusion = "QCAL CONFIRMED"
else:
    # No significant difference
    conclusion = "QCAL NOT CONFIRMED"
```

---

## 📁 File Structure

```
P-NP/
├── src/
│   └── vibro_fluorescence_qcal.py      # Main implementation (753 lines)
├── tests/
│   └── test_vibro_fluorescence_qcal.py # Test suite (765 lines, 56 tests)
├── examples/
│   └── demo_vibro_fluorescence_qcal.py # Demo with plots (486 lines)
└── VIBRO_FLUORESCENCE_QCAL_README.md   # Full documentation (453 lines)
```

---

## ✅ Verification

### All Tests Pass
```bash
$ python -m pytest tests/test_vibro_fluorescence_qcal.py -v
...
56 passed in 1.27s
```

### Demo Generates Plots
```bash
$ python examples/demo_vibro_fluorescence_qcal.py
...
✓ 6 plots saved to /tmp/
```

### Test Coverage
- ✓ Coupling Hamiltonian (4 tests)
- ✓ Spectral Formalism (8 tests)
- ✓ Protein Oscillator (5 tests)
- ✓ Fluorescence Transduction (4 tests)
- ✓ QCAL Predictions (7 tests)
- ✓ Experimental Protocol (5 tests)
- ✓ Falsification Controls (3 tests)
- ✓ Signal Processing (9 tests)
- ✓ State Equation (2 tests)
- ✓ Integration Tests (3 tests)
- ✓ Constants (5 tests)

**Total: 56/56 passing ✓**

---

## 📚 Documentation

- **Full README**: `VIBRO_FLUORESCENCE_QCAL_README.md`
- **In-code documentation**: All functions have docstrings with equations
- **Visual demos**: 6 interactive demonstrations

---

## 🎓 Key Concepts

### 1. Energy Conservation Control
All frequencies tested with **exactly the same total energy**:
```
E_total = ∫|Ψ(t)|²dt = constant ∀ ωₚ
```

### 2. Spectral Selectivity
QCAL predicts enhancement at specific frequencies:
- ω₀ = 141.7001 Hz (fundamental)
- ω₀/2 = 70.85 Hz (2nd harmonic)
- ω₀/3 = 47.23 Hz (3rd harmonic)
- ω₀×17/13 = 185.3 Hz (Magicicada ratio)

### 3. Statistical Rigor
ANOVA test with strict significance (α = 0.001):
- Compares resonant vs non-resonant frequencies
- Requires F_stat > F_critical to reject H₀
- p-value quantifies evidence strength

### 4. Falsifiability
Clear, measurable prediction:
- **If QCAL correct**: Peaks at resonances (ratio > 1.5)
- **If QCAL wrong**: Flat response (ratio ≈ 1.0)

---

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frequency**: 141.7001 Hz ∞³  
**Date**: 2026-01-27

---

## 🔗 See Also

- Full documentation: `VIBRO_FLUORESCENCE_QCAL_README.md`
- Source code: `src/vibro_fluorescence_qcal.py`
- Test suite: `tests/test_vibro_fluorescence_qcal.py`
- Demo: `examples/demo_vibro_fluorescence_qcal.py`
