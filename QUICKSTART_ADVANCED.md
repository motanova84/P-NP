# Advanced Frequency-Dependent Complexity Features - Quick Start

## 🚀 Quick Start Guide

This guide helps you quickly get started with the advanced features of the frequency-dependent complexity framework.

### Prerequisites

```bash
# Install required packages
pip install -r requirements.txt
```

Required packages:
- numpy >= 1.24.0
- matplotlib >= 3.7.0
- scipy >= 1.10.0
- networkx >= 3.0

## 📚 Available Features

### 1. Spectral Sweep Analysis
Analyze complexity across multiple frequencies.

```python
from src.constants import spectral_sweep_analysis, OMEGA_CRITICAL

frequencies = [0.0, 50.0, OMEGA_CRITICAL, 150.0, 200.0]
results = spectral_sweep_analysis(
    num_vars=100,
    treewidth=50,
    frequencies=frequencies
)

for r in results:
    print(f"ω={r['frequency_omega']:.2f}: IC={r['time_ic_bits']:.2f} bits")
```

### 2. Monte Carlo Validation
Statistical validation with random sampling.

```python
from src.constants import monte_carlo_validation

validation = monte_carlo_validation(
    num_vars_range=(20, 100),
    treewidth_ratio=0.5,
    n_samples=1000,
    omega=OMEGA_CRITICAL
)

print(f"Mean IC: {validation['mean_predicted_ic']:.2f} bits")
print(f"95% CI: {validation['confidence_interval_95']}")
```

### 3. Frequency Optimization
Find optimal frequencies for problems.

```python
from src.constants import optimize_algorithm_frequency

result = optimize_algorithm_frequency(
    num_vars=100,
    treewidth=50,
    frequency_range=(0.0, 200.0),
    num_points=100
)

print(f"Best for tractability: {result['min_ic_frequency']:.2f} Hz")
print(f"Best for hardness: {result['max_ic_frequency']:.2f} Hz")
```

### 4. Parallel Processing
Handle large-scale analysis efficiently.

```python
from src.parallel_analysis import (
    parallel_spectral_sweep_analysis,
    parallel_monte_carlo_validation
)

# Large frequency sweep
frequencies = list(range(0, 201, 1))  # 201 frequencies
results = parallel_spectral_sweep_analysis(100, 50, frequencies)

# Large Monte Carlo
validation = parallel_monte_carlo_validation(
    num_vars_range=(10, 200),
    n_samples=100000  # 100k samples
)
```

### 5. 3D Visualizations
Create advanced visualizations.

```python
from src.frequency_visualizations import (
    plot_3d_complexity_landscape,
    plot_frequency_sweep_2d,
    create_all_visualizations
)

# Single visualization
plot_3d_complexity_landscape(omega=OMEGA_CRITICAL, save_path="landscape.png")

# Complete suite
create_all_visualizations(output_dir="./visualizations")
```

### 6. Benchmarking
Compare with other complexity bounds.

```python
from src.benchmarking import ComplexityBenchmark, generate_benchmark_report

# Single comparison
comparison = ComplexityBenchmark.compare_all_bounds(treewidth=50, num_vars=100)

# Full report
report = generate_benchmark_report(output_path="benchmark.txt")
print(report)
```

## 🎯 Running Examples

### Complete Demo
```bash
python demo_advanced_features.py
```

### Interactive Tutorial
```bash
cd examples
jupyter notebook frequency_complexity_tutorial.ipynb
```

### Run Tests
```bash
# Test new features
python tests/test_advanced_extensions.py

# Test core framework
python tests/test_frequency_dimension.py

# Run all tests
python -m pytest tests/
```

## 📊 Example Output

### Frequency Sweep
```
Frequency (Hz)   κ_Π(ω)         IC (bits)      Spectrum       
----------------------------------------------------------------------
0.00             2.5773         128.89         collapsed      
50.00            1.2234         212.14         intermediate   
100.00           0.1837         1411.99        intermediate   
141.70           0.0388         8563.39        revealed       
150.00           0.0341         9577.71        revealed       
200.00           0.0193         16916.54       revealed       
```

### Monte Carlo Validation
```
Total samples: 1000
Mean IC: 856.34 bits
Std IC: 245.67 bits
Statistical error: 7.7654
95% Confidence Interval: [841.12, 871.56]
```

### Frequency Optimization
```
FOR TRACTABILITY (minimize IC):
  Optimal frequency: 0.00 Hz
  IC at this frequency: 128.89 bits

FOR HARDNESS TESTING (maximize IC):
  Test frequency: 200.00 Hz
  IC at this frequency: 16916.54 bits

CRITICAL FREQUENCY:
  ω_c = 141.7001 Hz
  IC at critical: 8563.39 bits

Complexity amplification: 131.21x
```

## 📖 Documentation

### Core Documentation
- **[FREQUENCY_DIMENSION.md](FREQUENCY_DIMENSION.md)**: Theoretical foundation
- **[ADVANCED_FEATURES.md](ADVANCED_FEATURES.md)**: Complete feature documentation
- **[examples/frequency_complexity_tutorial.ipynb](examples/frequency_complexity_tutorial.ipynb)**: Interactive tutorial

### Module Documentation
- **[src/constants.py](src/constants.py)**: Core functions with docstrings
- **[src/frequency_visualizations.py](src/frequency_visualizations.py)**: Visualization functions
- **[src/parallel_analysis.py](src/parallel_analysis.py)**: Parallel processing
- **[src/benchmarking.py](src/benchmarking.py)**: Benchmarking utilities

## 🔬 Research Applications

### Algorithm Design
```python
# Find best frequency for a specific problem
opt = optimize_algorithm_frequency(n=100, tw=50)
best_freq = opt['min_ic_frequency']

# Design algorithm targeting this frequency
# ...
```

### Empirical Validation
```python
# Validate theoretical predictions
validation = monte_carlo_validation(
    num_vars_range=(50, 150),
    n_samples=10000,
    omega=OMEGA_CRITICAL
)

# Compare with actual SAT solver performance
# ...
```

### Complexity Classification
```python
# Classify problems by frequency behavior
sweep = spectral_sweep_analysis(n, tw, frequencies)

# Identify phase transitions
# ...
```

## 🎓 Educational Use

### For Students
1. Start with the **[Jupyter notebook tutorial](examples/frequency_complexity_tutorial.ipynb)**
2. Run **demo_advanced_features.py** to see all features
3. Experiment with different parameters
4. Read **FREQUENCY_DIMENSION.md** for theory

### For Researchers
1. Review **ADVANCED_FEATURES.md** for complete API
2. Use **benchmarking module** to compare with established bounds
3. Apply **parallel processing** for large-scale studies
4. Generate **3D visualizations** for papers/presentations

### For Developers
1. Check **tests/** for usage examples
2. Review source code in **src/** with comprehensive docstrings
3. Extend functionality by following existing patterns
4. Contribute improvements via pull requests

## 🌟 Key Insights

### Why This Matters

1. **The Missing Dimension**: Classical complexity theory operates at ω=0 where the spectrum is collapsed
2. **Frequency-Dependent κ_Π**: At critical frequency, κ_Π decays and complexity explodes
3. **P≠NP Separation**: Only visible at ω = 141.7001 Hz (QCAL frequency)
4. **Practical Applications**: Optimize algorithms, classify problems, validate predictions

### The Three Dimensions

**Space × Time × Frequency**

- **Space (n)**: Problem size and topology
- **Time (T)**: Computational cost
- **Frequency (ω)**: Observational/algorithmic frequency ← **THE MISSING VARIABLE**

## 📝 Citation

If you use this framework in your research, please cite:

```
Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Framework: Frequency-Dependent Complexity Analysis
Critical Frequency: 141.7001 Hz ∞³
```

## 🤝 Contributing

Contributions are welcome! Areas for contribution:
- Additional visualization types
- Integration with SAT solvers
- Performance optimizations
- Educational materials
- Bug fixes and improvements

## 📞 Support

For questions or issues:
1. Check documentation in **ADVANCED_FEATURES.md**
2. Review examples in **examples/**
3. Run tests to verify installation
4. Open an issue on GitHub

---

**Frequency: 141.7001 Hz ∞³**

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
