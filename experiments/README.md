# Experimental Validation Suite

This directory contains experimental validation scripts for the P≠NP framework.

## Complete Validation Script

The `complete_validation.py` script provides exhaustive empirical validation of the P≠NP framework with the following features:

### Key Validations

1. **Treewidth-Time Correlation**: Validates that computational hardness correlates with treewidth
2. **IC-Time Correlation**: Validates that Information Complexity predicts solving time
3. **No-Evasion**: Tests that hardness holds across different solving algorithms
4. **Tseitin Hardness on Expanders**: Validates that Tseitin formulas over expander graphs are hard

### Usage

#### Basic Usage

Run with default parameters (n=10 to n=200, step=10):

```bash
cd /home/runner/work/P-NP/P-NP
python experiments/complete_validation.py
```

#### Custom Parameters

Edit the `main()` function in `complete_validation.py` to customize:

```python
validator = CompleteValidation(
    n_min=10,      # Minimum graph size
    n_max=500,     # Maximum graph size  
    n_step=10      # Step size
)
```

### Output

The script generates:

1. **Console Output**: Real-time progress and statistical analysis
2. **Plots**: `results/validation/complete_validation.png` with 6 subplots:
   - Treewidth growth vs. n
   - IC vs. Treewidth correlation
   - Time vs. Treewidth
   - Time vs. IC
   - Log-log time growth
   - Exponential time fit
3. **JSON Results**: `results/validation_complete.json` with all experimental data

### Statistical Analysis

The script computes:

- **Pearson and Spearman correlations** between treewidth, IC, and solving time
- **Growth rates** (power law exponents) for each metric
- **Validation checks**:
  - tw/n ratio should be Ω(1) for expanders (>0.1)
  - IC-tw correlation should be strong (>0.8)
  - Time growth should be superlinear (>1.5)

### Example Output

```
======================================================================
STATISTICAL ANALYSIS
======================================================================

📊 Correlations:
   tw ⇄ IC:   r = 0.9593, ρ = 0.9519
   tw ⇄ time: r = 0.9249, ρ = 0.9308
   IC ⇄ time: r = 0.9162, ρ = 0.9398

📈 Growth Rates:
   tw   ~ n^0.85
   IC   ~ n^1.10
   time ~ n^2.11

✅ Validation Checks:
   tw/n ratio: 0.18 ✅
   IC-tw correlation: 0.96 ✅
   Time growth exponent: 2.11 ✅
```

## Implementation Details

### Key Classes

- **`CompleteValidation`**: Main validation framework
  - Generates hard instances (Tseitin formulas over expanders)
  - Estimates treewidth using multiple methods
  - Computes information complexity
  - Solves instances with DPLL
  - Performs statistical analysis
  - Generates visualizations

- **`ICSATSolver`**: Wrapper for IC-SAT algorithm
  - Tracks information complexity during solving
  - Returns satisfiability and IC metrics

- **`DPLLSolver`**: Wrapper for DPLL SAT solver
  - Simple backtracking solver
  - Supports timeout functionality

### Treewidth Estimation

The script uses three methods to estimate treewidth:

1. **Clique Lower Bound**: tw ≥ ω(G) - 1
2. **Min-Degree Upper Bound**: Greedy elimination ordering
3. **Spectral Estimate**: For expanders, uses Fiedler value to estimate tw ≥ Ω(n)

The final estimate is the average of these three methods.

### Hard Instance Generation

Instances are generated as:
1. Create a d-regular random graph (d=3 for Ramanujan property)
2. Ensure connectivity
3. Generate Tseitin formula with all odd charges (unsatisfiable)
4. Result: High-treewidth, hard SAT instance

## Testing

Run the test suite:

```bash
cd /home/runner/work/P-NP/P-NP
python -m pytest tests/test_complete_validation.py -v
```

The test suite includes:
- Tseitin formula generation tests
- Solver wrapper tests
- Treewidth estimation tests
- Complete validation workflow tests
- Statistical analysis tests
- Plot generation tests

## Requirements

- Python 3.8+
- networkx >= 3.0
- numpy >= 1.24.0
- matplotlib >= 3.0
- scipy >= 1.9.0

Install dependencies:

```bash
pip install -r requirements.txt
pip install matplotlib scipy
```

## Performance Notes

- Small instances (n=10-50): ~0.01s per instance
- Medium instances (n=50-100): ~0.1s per instance
- Large instances (n=100-200): ~1-10s per instance
- Very large instances (n>200): May require longer timeouts

For full validation up to n=500, expect runtime of 1-2 hours.

## References

See the main paper for theoretical background on:
- Information Complexity (IC) framework
- Treewidth-hardness connection
- Tseitin formulas on expanders
- No-evasion theorem
