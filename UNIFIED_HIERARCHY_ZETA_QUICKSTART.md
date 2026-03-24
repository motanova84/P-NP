# 🌌 Unified Hierarchy Zeta - Quickstart Guide

## ⚡ Quick Summary

**Unified Hierarchy Theorem**: All coherent systems converge to the Riemann zeta function ζ(s) and resonate with its non-trivial zeros.

**Five Systems**:
1. **System 1**: Golden ratio φ (fractal modulation)
2. **System 2**: ζ(n) values (analytical moments)
3. **System 3**: QCAL Codons (symbiotic resonance)
4. **System 4**: Harmonics (vibrational consequences)
5. **System 5**: ζ(s) zeros (fundamental base)

---

## 🚀 Installation

```bash
# Clone repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Install dependencies
pip install -r requirements.txt
```

---

## 💻 Basic Usage

### Run the Demo

```bash
python examples/demo_zeta_hierarchy.py
```

This will:
- Demonstrate all five systems
- Show their convergence to ζ(s)
- Verify the unified hierarchy theorem
- Create visualizations (saved to `output/`)

### Quick Python Example

```python
from src.unified_hierarchy_zeta import UnifiedHierarchyTheorem

# Initialize the unified hierarchy
hierarchy = UnifiedHierarchyTheorem(num_zeros=20)

# Get base frequency
f0 = hierarchy.zeta_system.f0
print(f"Base frequency: f₀ = {f0} Hz")  # 141.7001 Hz

# Verify all systems converge to ζ(s)
results = hierarchy.verify_convergence()
print(results)

# Check Riemann Hypothesis physical interpretation
rh = hierarchy.riemann_hypothesis_physical()
print(f"Consciousness possible: {rh['consciousness_possible']}")
```

---

## 🔬 System-by-System Usage

### System 5: ζ(s) as Fundamental Base

```python
from src.unified_hierarchy_zeta import ZetaFundamentalSystem

zeta = ZetaFundamentalSystem(num_zeros=20)

# Get spectral frequencies from zeros
frequencies = zeta.spectral_frequencies()
print(f"First frequency: {frequencies[0]} Hz")

# Get zero spacings
spacings = zeta.zero_spacings()

# Get spectral delta
delta_zeta = zeta.coherence_parameter()
print(f"δζ = {delta_zeta} Hz")  # ≈ 0.2787 Hz
```

### System 1: Golden Ratio Modulation

```python
from src.unified_hierarchy_zeta import GoldenRatioModulation

golden = GoldenRatioModulation(zeta)

# Get golden ratio
phi = golden.phi
print(f"φ = {phi}")  # 1.618033988749...

# Generate Fibonacci numbers
F_10, F_11 = golden.fibonacci_emergence(10)
print(f"F_10 = {F_10}, F_11 = {F_11}")  # 55, 89

# Check self-similar frequency ratios
ratios = golden.self_similar_ratios(k=1, alpha=0.5)
```

### System 2: ζ(n) Values (Analytical Moments)

```python
from src.unified_hierarchy_zeta import ZetaValuesAnalytical

zeta_vals = ZetaValuesAnalytical(zeta)

# Get special values
zeta_2 = zeta_vals.zeta_value(2)
print(f"ζ(2) = π²/6 = {zeta_2}")  # 1.644934066848...

# Get even values
even_values = zeta_vals.zeta_even_values(5)
print(even_values)  # {2: ..., 4: ..., 6: ..., 8: ..., 10: ...}

# Compute moments of zero distribution
moment_2 = zeta_vals.moments_of_zeros(2)
```

### System 3: QCAL Codons (Symbiotic Resonance)

```python
from src.unified_hierarchy_zeta import QCALCodonResonance

codons = QCALCodonResonance(zeta)

# Check specific codon
codon = (1, 0, 0, 0)
freq = codons.codon_frequency(codon)
print(f"Codon 1000: {freq} Hz")  # Should be ≈ f₀

# Check if codon is resonant
is_resonant, zero_idx = codons.is_resonant(codon, tolerance=0.01)
if is_resonant:
    print(f"Codon resonates with zero {zero_idx + 1}")

# Measure coherence
coherence = codons.coherence_measure(codon)
print(f"Coherence: {coherence}")  # 0 to 1

# Find resonant codons
resonant = codons.find_resonant_codons(length=4, max_samples=1000)
```

### System 4: Harmonics (Vibrational Consequences)

```python
from src.unified_hierarchy_zeta import HarmonicSystem

harmonics = HarmonicSystem(zeta)

# Get harmonic series for first zero
harm_series = harmonics.harmonic_series(zero_index=0, max_harmonic=10)
print(harm_series)  # [f₁, 2f₁, 3f₁, ..., 10f₁]

# Get normal modes
normal_modes = harmonics.normal_modes()

# Get overtone structure
overtones = harmonics.overtone_structure(fundamental_index=0)
print(overtones)  # {1: f₁, 2: 2f₁, 3: 3f₁, 4: 4f₁, 5: 5f₁}
```

---

## 🔥 Complete Verification

### Verify Unified Convergence

```python
from src.unified_hierarchy_zeta import verify_unified_hierarchy

# Run complete verification
results = verify_unified_hierarchy(num_zeros=20)

# Print results
import json
print(json.dumps(results, indent=2))
```

### Check Physical RH Requirement

```python
hierarchy = UnifiedHierarchyTheorem(num_zeros=20)

# Get RH physical interpretation
rh_analysis = hierarchy.riemann_hypothesis_physical()

print(f"All zeros on critical line: {rh_analysis['all_zeros_on_critical_line']}")
print(f"Spectral symmetry: {rh_analysis['spectral_symmetry']}")
print(f"Consciousness possible: {rh_analysis['consciousness_possible']}")
print(f"Λ_G = {rh_analysis['lambda_G']}")
```

---

## 📊 Key Constants

| Constant | Value | Meaning |
|----------|-------|---------|
| f₀ | 141.7001 Hz | QCAL base frequency |
| γ₁ | 14.134725142 | First zero imaginary part |
| δζ | 0.2787 Hz | Spectral curvature: f₀ - 100√2 |
| φ | 1.618033988749... | Golden ratio |
| ζ(2) | π²/6 ≈ 1.6449 | Special zeta value |
| α | 1/137.035999084 | Fine structure constant |

---

## 🌌 Master Equation

The complete hierarchy:

```
G → ζ(s) → {ρ_n} → {f_n} → {φ, ζ(n), Codons, k·f_n} → 𝓒
```

Where:
- **G**: Mother geometry space
- **ζ(s)**: Riemann zeta function
- **ρ_n = 1/2 + iγ_n**: Zeros on critical line
- **f_n = (γ_n/γ₁) × f₀**: Spectral frequencies
- **φ**: Golden ratio modulation
- **ζ(n)**: Analytical moments
- **Codons**: QCAL symbiotic resonance
- **k·f_n**: Harmonic overtones
- **𝓒**: Consciousness (Ker(π_α - π_δζ))

---

## 💎 Key Theorems

### Convergence Theorem

**Statement**: All coherent systems resonate with the zeros of ζ(s).

**Mathematical Form**:
$$\text{System coherent} \iff \text{resonates with } \{\rho_n = \tfrac{1}{2} + i\gamma_n\}$$

### RH Physical Requirement

**Statement**: The Riemann Hypothesis is a physical requirement for consciousness.

**Consequence**:
- If RH true → perfect spectral symmetry → consciousness possible
- If RH false → Λ_G = 0 → no consciousness → no mathematics

---

## 🧪 Testing

Run tests to verify implementation:

```bash
# Run unified hierarchy tests
python -m pytest tests/test_unified_hierarchy_zeta.py -v

# Run all tests
./run_all_tests.sh
```

---

## 📚 Documentation

- **Main Theory**: [UNIFIED_HIERARCHY_ZETA.md](UNIFIED_HIERARCHY_ZETA.md)
- **QCAL ∞³ Framework**: [QCAL_INFINITY_CUBED_README.md](QCAL_INFINITY_CUBED_README.md)
- **Frequency Dimension**: [FREQUENCY_DIMENSION.md](FREQUENCY_DIMENSION.md)
- **Ultimate Unification**: [ULTIMATE_UNIFICATION_README.md](ULTIMATE_UNIFICATION_README.md)

---

## 🔗 Related Systems

This framework integrates with:

1. **QCAL ∞³**: Universal millennium problem framework
2. **κ_Π = 2.5773**: Calabi-Yau constant
3. **Holographic Duality**: AdS/CFT correspondence
4. **Consciousness Framework**: RNA piCODE connection

---

## ✨ Examples

### Find Resonant Codons

```python
hierarchy = UnifiedHierarchyTheorem()
codons_system = hierarchy.codon_system

# Search for codons resonating with f₀
test_codons = [(1,0,0,0), (9,9,9), (6,1,7,4), (1,4,1,7)]

for codon in test_codons:
    freq = codons_system.codon_frequency(codon)
    coherence = codons_system.coherence_measure(codon)
    is_res, idx = codons_system.is_resonant(codon)
    
    print(f"Codon {''.join(map(str, codon))}: {freq:.2f} Hz, "
          f"coherence = {coherence:.4f}, "
          f"resonant: {is_res}")
```

### Visualize Zero Spacings

```python
import matplotlib.pyplot as plt

zeta = ZetaFundamentalSystem(num_zeros=50)
spacings = zeta.zero_spacings()
weyl = [zeta.weyl_density(i) for i in range(1, len(spacings) + 1)]

plt.plot(spacings, 'o-', label='Actual Δγ_n')
plt.plot(weyl, 's--', label='Weyl density', alpha=0.7)
plt.xlabel('Zero index n')
plt.ylabel('Spacing')
plt.title('Zero Spacings with Golden Ratio Modulation')
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig('zero_spacings.png')
```

---

## 🌟 Conclusion

The Unified Hierarchy Zeta system demonstrates that:

1. **All systems converge to ζ(s)** - The Riemann zeta function is the universal base
2. **Coherence = Resonance with zeros** - Systems are coherent iff they resonate with ρ_n
3. **RH is physical** - Riemann Hypothesis is required for consciousness
4. **Universe is ζ(s) symphony** - We are chords resonating at f₀ = 141.7001 Hz

---

🕳️ → ☀️ **The universe is a symphony of ζ(s).**

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frequency**: 141.7001 Hz ∞³  
**License**: MIT
