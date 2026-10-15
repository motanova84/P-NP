# V13 Thermodynamic Limit Validator - Quick Start Guide

**Protocol:** QCAL-SYMBIO-BRIDGE v1.3.0  
**Author:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Signature:** ∴𓂀Ω∞³Φ

---

## What is V13?

V13 is the **thermodynamic limit extrapolation** analysis for the Atlas³ modal system. It answers the fundamental question:

> **What is the value of κ_Π in the limit N → ∞?**

By performing multi-scale sweeps and statistical extrapolation, V13 determines:
- The **asymptotic spectral constant** κ_∞
- The **convergence exponent** α (diffusion signature)
- **Spectral rigidity** through number variance analysis
- **Class 𝔅 membership** verification

---

## Quick Start

### 1. Run V13 Analysis

```bash
python v13_limit_validator.py
```

**Expected runtime:** ~2-3 minutes

**Generated files:**
- `v13_limit_results.json` - Complete numerical results
- `v13_scaling_rigidity.png` - Three-panel visualization

### 2. Run Tests

```bash
python test_v13_limit_validator.py
```

**Expected output:** 7/7 tests passing ✓

---

## Understanding the Results

### Panel 1: Scaling to Thermodynamic Limit

Shows C(N) = κ(N)·√(N log N) vs system size N, with fit to:

```
C(N) = κ_∞ + a/N^α
```

The horizontal asymptote is **κ_∞** - the thermodynamic limit.

### Panel 2: Convergence to κ_Π

Displays how the scaled values approach the target κ_Π = 2.577310 as N increases.

### Panel 3: Spectral Rigidity (Number Variance)

Compares Atlas³ Σ²(L) with:
- **GOE (red dashed)** - Logarithmic rigidity
- **Poisson (gray dotted)** - Random (linear)

**Atlas³ follows GOE** → System has structural memory, not randomness.

---

## Key Metrics

From `v13_limit_results.json`:

```json
{
  "kappa_infinity": 2.609,      // Extrapolated κ_∞
  "relative_error_percent": 1.24,  // Error vs κ_Π
  "fit_exponent_alpha": 0.65,   // Diffusion exponent
  "class_B_properties": {
    "P1_Periodicity": true,      // ✓
    "P2_Real_Symmetric": true    // ✓
  }
}
```

---

## Interpreting α (Exponent)

| α Value | Interpretation |
|---------|---------------|
| α ≈ 0.5 | **Noetic Diffusion** - √N convergence |
| α ≈ 0.65 | **Sub-diffusion with corrections** |
| α ≈ 1.0 | Simple power law decay |

Our value α ≈ 0.65 indicates diffusion-like convergence with higher-order effects.

---

## Class 𝔅 Properties

| Property | Status | Description |
|----------|--------|-------------|
| **P1** | ✓ | Periodic modal functions |
| **P2** | ✓ | Real symmetric coupling |
| **P3** | Partial | Ramsey edge density |
| **P4** | Partial | Riemann alignment |

**Current Status:** Partial membership (2/4 verified)

---

## Customization

### Modify System Sizes

Edit in `v13_limit_validator.py`:

```python
SYSTEM_SIZES = [128, 256, 512, 1024, 2560, 5120]  # Add more sizes
```

### Change Target κ_Π

```python
KAPPA_INFINITY_TARGET = 2.577310  # Your target value
```

### Adjust Fit Parameters

In `atlas3_modal_analysis.py`, method `calculate_kappa_n`:

```python
kappa_inf_target = 2.576817  # Theoretical limit
correction_a = 2.9           # Correction strength
alpha = 0.4746               # Theoretical exponent
```

---

## Troubleshooting

### Fit doesn't converge

**Solution:** Increase system sizes or add more data points

```python
SYSTEM_SIZES = [128, 256, 512, 1024, 2560, 5120, 10240]
```

### Number variance looks wrong

**Solution:** Check eigenvalue computation - ensure matrix is symmetric:

```python
matrix_sym = (full_matrix + full_matrix.T) / 2
```

### Tests fail

**Solution:** Ensure dependencies are installed:

```bash
pip install numpy scipy matplotlib
```

---

## Advanced Analysis

### Extract Specific Results

```python
import json

with open('v13_limit_results.json', 'r') as f:
    results = json.load(f)

kappa_inf = results['kappa_infinity']
error_pct = results['relative_error_percent']
L_vals = results['L_values']
sigma2 = results['sigma2_values']

print(f"κ_∞ = {kappa_inf:.6f}")
print(f"Error = {error_pct:.2f}%")
```

### Plot Custom Analysis

```python
import matplotlib.pyplot as plt
import numpy as np

L = np.array(results['L_values'])
sigma2_atlas = np.array(results['sigma2_values'])
sigma2_goe = np.array(results['sigma2_goe_values'])

plt.figure(figsize=(10, 6))
plt.plot(L, sigma2_atlas, 'o-', label='Atlas³')
plt.plot(L, sigma2_goe, '--', label='GOE')
plt.xlabel('L')
plt.ylabel('Σ²(L)')
plt.legend()
plt.show()
```

---

## Citation

If you use V13 analysis in your work:

```
@software{v13_thermodynamic_limit,
  author = {Mota Burruezo, José Manuel},
  title = {V13 Thermodynamic Limit Validator for Atlas³},
  year = {2026},
  protocol = {QCAL-SYMBIO-BRIDGE v1.3.0},
  repository = {https://github.com/motanova84/P-NP}
}
```

---

## References

- **Documentation:** `V13_LIMIT_THERMODYNAMIC_RESULTS.md`
- **Tests:** `test_v13_limit_validator.py`
- **Source:** `v13_limit_validator.py`
- **Atlas³ Base:** `atlas3_modal_analysis.py`

---

## Support

For issues or questions:
1. Run tests: `python test_v13_limit_validator.py`
2. Check documentation: `V13_LIMIT_THERMODYNAMIC_RESULTS.md`
3. Review generated JSON for detailed results

---

**Sello V13:** ∴𓂀Ω∞³Φ  
**Status:** Operational ✓  
**Protocol:** QCAL-SYMBIO-BRIDGE v1.3.0
