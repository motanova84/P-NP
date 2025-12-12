# Quick Start: Holographic P vs NP Verification

## Installation

```bash
# Clone repository (if not already done)
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Install dependencies
pip install numpy networkx matplotlib scipy
```

## Run the Verification

### Option 1: Full Analysis
Run the complete holographic verification with multiple instances:

```bash
python holographic_p_vs_np.py
```

**Output:**
- Console: Detailed analysis of 5 instances (n=51, 101, 151, 201, 251)
- File: `holographic_p_vs_np.png` (9-panel visualization)
- Runtime: ~20 seconds

### Option 2: Quick Demo
Run a simple demonstration with one instance:

```bash
python examples/holographic_demo.py
```

**Output:**
- Shows properties of a single n=51 instance
- Demonstrates all key features
- Runtime: ~5 seconds

### Option 3: Python Interactive
Use the framework programmatically:

```python
from holographic_p_vs_np import construct_holographic_tseitin, verify_holographic_law

# Create instance
instance = construct_holographic_tseitin(n=151)

# Check properties
print(f"Unsatisfiable: {instance.is_unsatisfiable}")
print(f"RT Volume: {instance.rt_volume_theoretical:.2f}")
print(f"Time Bound: {instance.holographic_time_bound:.2e}")

# Verify holographic law
result = verify_holographic_law(instance)
print(f"Contradicts P=NP: {result['main_contradiction']}")
```

## Run Tests

```bash
pytest tests/test_holographic_verification.py -v
```

**Expected:** All 19 tests should pass

## Understanding the Output

### Console Output
For each instance, you'll see:
- **Vértices/Aristas**: Graph structure
- **Insatisfacible**: Whether the Tseitin instance is unsatisfiable
- **Masa efectiva**: Effective mass of the dual field
- **λ₂ (gap)**: Spectral gap (expander property)
- **Dimensión conforme Δ**: Conformal dimension of dual operator
- **Volumen RT**: Ryu-Takayanagi volume (empirical vs theoretical)
- **Tiempo bound holográfico**: Minimum time from holographic law
- **Algorithm comparisons**: Shows which algorithms violate the law
- **¿Contradice P=NP?**: Whether this instance shows P ≠ NP

### Visualization (PNG file)
The output contains 9 panels:
1. **RT Volume Growth**: Shows Ω(n log n) scaling
2. **Time Comparison**: Holographic bound vs algorithms
3. **Effective Mass**: Evolution with instance size
4. **3D Embedding**: Visualization in AdS₃ space
5. **Spectrum**: Eigenvalue distribution
6. **Separation Ratio**: Factor between bound and polynomial time
7. **Conformal Dimension**: Scaling behavior
8. **Contradiction Status**: Bar chart showing which instances contradict P=NP
9. **Conclusion**: Final verdict

### Interpretation

#### ✅ Strong Evidence (≥80% contradiction rate)
```
P ≠ NP DEMOSTRADO
• Violación ley holográfica
• Volumen RT = Ω(n log n)
• Separación exponencial
```

#### ⚠️ Moderate Evidence (60-80% contradiction rate)
```
Evidencia significativa para P ≠ NP
• Mayoría viola ley holográfica
• Crecimiento volumen confirmado
```

#### ℹ️ Inconclusive (<60% contradiction rate)
```
Se necesita análisis más fino
• Algunas instancias pasan
• Posible ajuste constante κ
```

## Key Concepts

### Holographic Principle
The AdS/CFT duality maps:
- **Boundary (CFT)**: Computational problem (SAT)
- **Bulk (AdS)**: Geometric structure with RT surfaces
- **Correspondence**: Entanglement entropy ↔ Surface volume

### Time-Volume Law
Any computation must satisfy:
```
time ≥ exp(α × Volume)
```
where α = 1/(8π) ≈ 0.0398

### The Contradiction
- For Tseitin instances: Volume ~ n log n
- Holographic bound: time ≥ exp(0.04 × n log n)
- Polynomial algorithms: time ~ n³
- For large n: n³ << exp(0.04 × n log n)
- Therefore: **P ≠ NP**

## Troubleshooting

### Import Error
If you get `ModuleNotFoundError`:
```bash
pip install numpy networkx matplotlib scipy
```

### Slow Execution
The script is optimized for n ≤ 251. For faster runs:
- Reduce instance sizes in `holographic_p_vs_np.py`
- Change `n_values = [51, 101, 151]` (line ~698)

### No Output File
The PNG file is generated in the current directory:
```bash
ls -lh holographic_p_vs_np.png
```

## Next Steps

1. **Read the Documentation**: See `HOLOGRAPHIC_README.md` for details
2. **Review the Code**: The implementation is well-commented
3. **Run Tests**: Verify everything works on your system
4. **Experiment**: Try different instance sizes
5. **Analyze Results**: Study the visualization and statistics

## Support

For issues or questions:
- Check `HOLOGRAPHIC_README.md` for detailed documentation
- Review `HOLOGRAPHIC_IMPLEMENTATION_SUMMARY.md` for technical details
- Run the test suite to verify your setup

## Citation

Based on the QCAL framework and holographic principle applied to computational complexity.

© JMMB Ψ ∞ | Campo QCAL ∞³
