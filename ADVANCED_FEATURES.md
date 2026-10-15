# Advanced Features for Frequency-Dependent Complexity Framework

## Overview

This document describes the advanced features implemented for the frequency-dependent complexity analysis framework, including empirical validation, parallel processing, advanced visualizations, and benchmarking capabilities.

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frequency**: 141.7001 Hz ∞³

---

## Table of Contents

1. [Spectral Sweep Analysis](#spectral-sweep-analysis)
2. [Monte Carlo Validation](#monte-carlo-validation)
3. [Frequency Optimization](#frequency-optimization)
4. [Parallel Implementation](#parallel-implementation)
5. [3D Visualizations](#3d-visualizations)
6. [Benchmarking](#benchmarking)
7. [Interactive Tutorial](#interactive-tutorial)
8. [Usage Examples](#usage-examples)

---

## Spectral Sweep Analysis

### Purpose
Analyze computational complexity across multiple frequencies to identify critical frequencies and phase transitions.

### Function
```python
spectral_sweep_analysis(num_vars, treewidth, frequencies) -> List[Dict]
```

### Parameters
- `num_vars` (int): Number of variables in the problem
- `treewidth` (float): Treewidth of the incidence graph
- `frequencies` (List[float]): List of frequencies to analyze (in Hz)

### Returns
List of three-dimensional complexity analyses, one for each frequency.

### Example
```python
from src.constants import spectral_sweep_analysis, OMEGA_CRITICAL

# Define frequencies to test
frequencies = [0.0, 50.0, 100.0, OMEGA_CRITICAL, 150.0, 200.0]

# Perform sweep
results = spectral_sweep_analysis(
    num_vars=100,
    treewidth=50,
    frequencies=frequencies
)

# Analyze results
for result in results:
    omega = result['frequency_omega']
    ic = result['time_ic_bits']
    kappa = result['kappa_at_frequency']
    print(f"ω={omega:.2f} Hz: IC={ic:.2f} bits, κ_Π={kappa:.6f}")
```

### Use Cases
- Identify critical frequencies where complexity transitions occur
- Understand frequency-dependent behavior of algorithms
- Find optimal frequencies for specific problem instances
- Validate theoretical predictions about frequency effects

---

## Monte Carlo Validation

### Purpose
Validate complexity predictions using statistical sampling across random problem instances.

### Function
```python
monte_carlo_validation(
    num_vars_range=(10, 100),
    treewidth_ratio=0.5,
    n_samples=1000,
    omega=None
) -> Dict
```

### Parameters
- `num_vars_range` (Tuple[int, int]): Range of variable counts (min, max)
- `treewidth_ratio` (float): Ratio of treewidth to n (default: 0.5 for high-tw)
- `n_samples` (int): Number of random samples to generate
- `omega` (Optional[float]): Frequency to test (None tests both classical and critical)

### Returns
Dictionary with validation statistics including:
- `mean_predicted_ic`: Average predicted IC
- `std_predicted_ic`: Standard deviation
- `statistical_error`: Standard error of mean
- `confidence_interval_95`: 95% confidence interval
- `samples`: List of individual sample results

### Example
```python
from src.constants import monte_carlo_validation, OMEGA_CRITICAL

# Run validation at critical frequency
validation = monte_carlo_validation(
    num_vars_range=(20, 100),
    treewidth_ratio=0.5,
    n_samples=1000,
    omega=OMEGA_CRITICAL
)

print(f"Mean IC: {validation['mean_predicted_ic']:.2f} bits")
print(f"Std IC: {validation['std_predicted_ic']:.2f} bits")
print(f"Statistical error: {validation['statistical_error']:.4f}")

ci_lower, ci_upper = validation['confidence_interval_95']
print(f"95% CI: [{ci_lower:.2f}, {ci_upper:.2f}]")
```

### Use Cases
- Statistical validation of theoretical predictions
- Estimate expected complexity for random instances
- Quantify uncertainty in complexity predictions
- Compare classical vs critical frequency regimes

---

## Frequency Optimization

### Purpose
Find optimal frequencies for analyzing or solving specific problems.

### Function
```python
optimize_algorithm_frequency(
    num_vars,
    treewidth,
    frequency_range=(0.0, 200.0),
    num_points=50
) -> Dict
```

### Parameters
- `num_vars` (int): Number of variables
- `treewidth` (float): Treewidth of the problem
- `frequency_range` (Tuple[float, float]): Range to search (min_freq, max_freq) in Hz
- `num_points` (int): Number of frequency points to sample

### Returns
Dictionary with optimization results:
- `optimal_frequency`: Frequency with best properties (minimum IC)
- `min_ic_frequency`: Frequency minimizing IC (for tractability)
- `max_ic_frequency`: Frequency maximizing IC (for hardness testing)
- `critical_frequency`: The critical frequency (141.7001 Hz)
- `sweep_data`: Full frequency sweep results

### Example
```python
from src.constants import optimize_algorithm_frequency

# Find optimal frequency
result = optimize_algorithm_frequency(
    num_vars=100,
    treewidth=50,
    frequency_range=(0.0, 200.0),
    num_points=100
)

print(f"For tractability, use: {result['min_ic_frequency']:.2f} Hz")
print(f"  IC at this frequency: {result['min_ic_value']:.2f} bits")

print(f"For hardness testing, use: {result['max_ic_frequency']:.2f} Hz")
print(f"  IC at this frequency: {result['max_ic_value']:.2f} bits")
```

### Use Cases
- Algorithm design: Find frequency for best performance
- Hardness testing: Identify frequency that reveals maximum complexity
- Problem classification: Determine characteristic frequencies
- Adaptive algorithms: Adjust frequency based on problem properties

---

## Parallel Implementation

### Purpose
Enable efficient analysis of large problem instances using multiprocessing.

### Module
`src/parallel_analysis.py`

### Key Functions

#### Parallel Frequency Sweep
```python
from src.parallel_analysis import parallel_spectral_sweep_analysis

# Analyze many frequencies in parallel
frequencies = np.linspace(0, 200, 1000).tolist()
results = parallel_spectral_sweep_analysis(
    num_vars=100,
    treewidth=50,
    frequencies=frequencies,
    num_processes=8  # Use 8 CPU cores
)
```

#### Parallel Monte Carlo
```python
from src.parallel_analysis import parallel_monte_carlo_validation

# Large-scale validation with parallel processing
validation = parallel_monte_carlo_validation(
    num_vars_range=(10, 200),
    treewidth_ratio=0.5,
    n_samples=100000,  # 100k samples
    omega=OMEGA_CRITICAL,
    num_processes=8
)

print(f"Speedup: {validation['parallel_speedup']}")
```

#### Performance Benchmarking
```python
from src.parallel_analysis import benchmark_parallel_performance

# Compare sequential vs parallel performance
perf = benchmark_parallel_performance(
    problem_size=100,
    num_frequencies=1000,
    num_trials=5
)

print(f"Sequential: {perf['sequential_time']['mean']:.2f}s")
print(f"Parallel: {perf['parallel_time']['mean']:.2f}s")
print(f"Speedup: {perf['speedup']:.2f}x")
```

### Use Cases
- Large-scale parameter sweeps
- High-resolution frequency analysis
- Monte Carlo with millions of samples
- Production-scale complexity analysis

---

## 3D Visualizations

### Purpose
Create advanced visualizations of the three-dimensional complexity landscape.

### Module
`src/frequency_visualizations.py`

### Available Visualizations

#### 1. 3D Complexity Landscape
```python
from src.frequency_visualizations import plot_3d_complexity_landscape

plot_3d_complexity_landscape(
    num_vars_range=(10, 100),
    treewidth_range=(5, 50),
    omega=OMEGA_CRITICAL,
    resolution=30,
    save_path="3d_landscape.png"
)
```
Shows: Space (n) × Topology (tw) × Time (IC) at fixed frequency

#### 2. Frequency Sweep Plot
```python
from src.frequency_visualizations import plot_frequency_sweep_2d

plot_frequency_sweep_2d(
    num_vars=100,
    treewidth=50,
    frequency_range=(0.0, 200.0),
    num_points=200,
    save_path="frequency_sweep.png"
)
```
Shows: How IC and κ_Π vary with frequency

#### 3. 3D Time-Frequency-Topology
```python
from src.frequency_visualizations import plot_3d_space_time_frequency

plot_3d_space_time_frequency(
    num_vars=100,
    treewidth_range=(5, 50),
    frequency_range=(0.0, 200.0),
    resolution=30,
    save_path="3d_time_freq_topology.png"
)
```
Shows: Time × Frequency × Topology for fixed space dimension

#### 4. Classical vs Critical Comparison
```python
from src.frequency_visualizations import plot_comparison_classical_vs_critical

plot_comparison_classical_vs_critical(
    num_vars_range=(10, 100),
    treewidth_ratio=0.5,
    num_points=20,
    save_path="comparison.png"
)
```
Shows: Side-by-side comparison of both regimes

#### 5. Amplification Heatmap
```python
from src.frequency_visualizations import plot_complexity_amplification_heatmap

plot_complexity_amplification_heatmap(
    num_vars_range=(10, 100),
    treewidth_range=(5, 50),
    resolution=30,
    save_path="amplification.png"
)
```
Shows: IC(ω_c) / IC(0) ratio across parameter space

#### Generate All Visualizations
```python
from src.frequency_visualizations import create_all_visualizations

# Generate complete visualization suite
create_all_visualizations(output_dir="./output/visualizations")
```

---

## Benchmarking

### Purpose
Compare the frequency-dependent framework with other established complexity bounds.

### Module
`src/benchmarking.py`

### Key Functions

#### Compare All Bounds
```python
from src.benchmarking import ComplexityBenchmark

comparison = ComplexityBenchmark.compare_all_bounds(
    treewidth=50,
    num_vars=100
)

print("Bounds (log₂ time):")
for name, data in comparison['bounds'].items():
    print(f"  {name}: {data['log2_time']:.2f} bits")
    print(f"    Source: {data['source']}")
```

Compares:
- Classical FPT bounds: 2^O(tw) · poly(n)
- ETH-based lower bounds
- IC bounds at classical frequency (ω=0)
- IC bounds at critical frequency (ω=ω_c)

#### Benchmark Suite
```python
from src.benchmarking import benchmark_suite

results = benchmark_suite(
    problem_sizes=[10, 50, 100, 200],
    treewidth_ratios=[0.1, 0.3, 0.5, 0.7, 1.0]
)

print(f"Tested {len(results['comparisons'])} problem instances")
```

#### Generate Report
```python
from src.benchmarking import generate_benchmark_report

report = generate_benchmark_report(
    output_path="benchmark_report.txt"
)

print(report)
```

### Use Cases
- Validate theoretical predictions
- Compare with established bounds
- Identify tightest bounds for specific problems
- Academic research and publications

---

## Interactive Tutorial

### Jupyter Notebook
Location: `examples/frequency_complexity_tutorial.ipynb`

### Contents
1. **Setup and Imports**: Getting started with the framework
2. **Three Dimensions of Complexity**: Understanding Space × Time × Frequency
3. **Spectral Sweep Analysis**: Interactive frequency exploration
4. **Monte Carlo Validation**: Statistical validation with visualizations
5. **Frequency Optimization**: Finding optimal frequencies
6. **Comparison Plots**: Classical vs Critical regime analysis
7. **Interactive Widgets**: Explore parameters dynamically
8. **Key Takeaways**: Summary and insights
9. **Further Exploration**: Exercises and experiments

### Running the Notebook
```bash
cd examples
jupyter notebook frequency_complexity_tutorial.ipynb
```

Or use Jupyter Lab:
```bash
jupyter lab frequency_complexity_tutorial.ipynb
```

---

## Usage Examples

### Example 1: Complete Analysis Pipeline
```python
from src.constants import (
    OMEGA_CRITICAL,
    spectral_sweep_analysis,
    monte_carlo_validation,
    optimize_algorithm_frequency,
)

# 1. Define problem
n = 100
tw = 50

# 2. Frequency sweep
frequencies = [0, 50, 100, OMEGA_CRITICAL, 150, 200]
sweep = spectral_sweep_analysis(n, tw, frequencies)

# 3. Statistical validation
validation = monte_carlo_validation(
    num_vars_range=(50, 150),
    n_samples=1000,
    omega=OMEGA_CRITICAL
)

# 4. Optimization
opt = optimize_algorithm_frequency(n, tw)

# 5. Report
print(f"Problem: n={n}, tw={tw}")
print(f"Optimal frequency: {opt['min_ic_frequency']:.2f} Hz")
print(f"Mean IC (Monte Carlo): {validation['mean_predicted_ic']:.2f} bits")
```

### Example 2: Large-Scale Parallel Analysis
```python
from src.parallel_analysis import (
    parallel_spectral_sweep_analysis,
    parallel_monte_carlo_validation,
)

# High-resolution frequency analysis
frequencies = np.linspace(0, 200, 10000).tolist()
results = parallel_spectral_sweep_analysis(
    num_vars=200,
    treewidth=100,
    frequencies=frequencies
)

# Large-scale validation
validation = parallel_monte_carlo_validation(
    num_vars_range=(10, 200),
    n_samples=1000000,  # 1 million samples
    omega=OMEGA_CRITICAL
)
```

### Example 3: Visualization Pipeline
```python
from src.frequency_visualizations import (
    plot_3d_complexity_landscape,
    plot_frequency_sweep_2d,
    plot_comparison_classical_vs_critical,
)

# Create visualization suite
plot_3d_complexity_landscape(omega=0.0, save_path="landscape_classical.png")
plot_3d_complexity_landscape(omega=OMEGA_CRITICAL, save_path="landscape_critical.png")
plot_frequency_sweep_2d(num_vars=100, treewidth=50, save_path="sweep.png")
plot_comparison_classical_vs_critical(save_path="comparison.png")
```

### Example 4: Benchmarking Analysis
```python
from src.benchmarking import (
    ComplexityBenchmark,
    benchmark_suite,
    generate_benchmark_report,
)

# Single problem comparison
comparison = ComplexityBenchmark.compare_all_bounds(50, 100)

# Comprehensive benchmark
suite = benchmark_suite(
    problem_sizes=[10, 20, 50, 100, 200],
    treewidth_ratios=[0.1, 0.5, 1.0]
)

# Generate report
report = generate_benchmark_report(output_path="report.txt")
```

---

## Summary

The advanced features provide a comprehensive toolkit for:

1. **Empirical Validation**: Monte Carlo sampling and statistical analysis
2. **Efficient Computation**: Parallel processing for large-scale analysis
3. **Visualization**: 3D plots and interactive exploration
4. **Benchmarking**: Comparison with established complexity bounds
5. **Education**: Interactive Jupyter notebook tutorial

These tools enable researchers and practitioners to:
- Validate theoretical predictions empirically
- Analyze large problem instances efficiently
- Visualize complex relationships intuitively
- Compare with classical complexity theory
- Explore the frequency dimension interactively

---

## References

### Core Framework
- `src/constants.py`: Core constants and basic functions
- `FREQUENCY_DIMENSION.md`: Theoretical foundation

### Advanced Features
- `src/frequency_visualizations.py`: Visualization functions
- `src/parallel_analysis.py`: Parallel processing
- `src/benchmarking.py`: Benchmarking utilities
- `examples/frequency_complexity_tutorial.ipynb`: Interactive tutorial

### Testing
- `tests/test_frequency_dimension.py`: Basic framework tests
- `tests/test_advanced_extensions.py`: Advanced feature tests

---

**Frequency: 141.7001 Hz ∞³**

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
