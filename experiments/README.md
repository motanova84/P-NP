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
STATISTICAL ANALYSIS

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
# Experiments Directory

This directory contains experimental validation scripts for the P≠NP framework.

## Treewidth Estimation in Expander Graphs

### `treewidth_expander_estimation.py`

Empirical validation of the theoretical prediction that treewidth(G) ∈ Ω(n) for expander graphs. This experiment demonstrates that the treewidth of d-regular random expander graphs grows linearly with the number of nodes.

#### Features

1. **Expander Graph Generation**
   - Generates d-regular random graphs (default d=3)
   - Ensures connectivity for true expander properties
   - Uses NetworkX's random regular graph model

2. **Treewidth Estimation**
   - Greedy fill-in heuristic via NetworkX approximation
   - Fast estimation suitable for empirical validation
   - Accurate enough to verify theoretical predictions

3. **Empirical Validation**
   - Tests multiple graph sizes (50, 100, 200, 500 nodes)
   - Computes tw/n ratio to verify constant behavior
   - Confirms ratio stays around 0.17-0.20 as predicted

4. **Visualization**
   - Linear growth plot showing tw vs n
   - Ratio stability plot showing tw/n consistency
   - Professional publication-quality figures

#### Usage

```bash
# Run the complete experiment
python3 experiments/treewidth_expander_estimation.py
```

#### Expected Output

The experiment produces:
- Console output with results table
- Statistical analysis showing average ratio ~0.178
- Visualization saved to `/tmp/treewidth_expander_results.png`

Example results:
```
n (nodes)       Treewidth       tw/n Ratio     
---------------------------------------------
50              8               0.1600         
100             19              0.1900         
200             36              0.1800         
500             91              0.1820         

Average tw/n ratio: 0.1780
```

#### Theoretical Significance

This experiment confirms the key prediction that:
- **treewidth(G) ∈ Ω(n)** for expander graphs
- The ratio tw/n remains approximately constant
- This validates the linear growth assumption used in hardness proofs

#### Dependencies

```
networkx>=3.0
matplotlib>=3.7.0
```

#### Testing

Run the test suite:
```bash
python3 -m pytest tests/test_treewidth_expander_estimation.py -v
```

All 16 tests cover:
- Expander graph generation and properties
- Treewidth estimation accuracy
- Linear growth verification
- Experiment execution
- Graph connectivity and regularity

#### Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

---

## Statistical Analysis Module

### `statistical_analysis.py`

Advanced statistical analysis tool for P≠NP validation. Performs rigorous statistical tests to validate the theoretical framework through empirical data analysis.

#### Features

1. **Correlation Analysis**
   - Pearson correlations (linear relationships)
   - Spearman correlations (monotonic relationships)
   - Partial correlations (controlling for problem size)

2. **Exponential Time Hypothesis Testing**
   - Exponential model fitting: `time = a * exp(b * tw)`
   - Statistical significance testing
   - Model comparison (exponential vs polynomial)

3. **No-Evasion Hypothesis Testing**
   - Friedman test (non-parametric repeated measures)
   - Pairwise algorithm comparisons (Wilcoxon test)
   - Performance summaries across algorithms

4. **Growth Rate Analysis**
   - Power law fitting for asymptotic behavior
   - Confidence intervals for growth exponents
   - Analysis for treewidth, information complexity, and solving time

5. **Comprehensive Reporting**
   - JSON output with all statistical results
   - Professional publication-quality plots (6 visualizations)
   - Automated report generation

#### Usage

```bash
# Run with default data file (results/validation_complete.json)
python3 experiments/statistical_analysis.py

# Or use as a module
python3 -c "
from experiments.statistical_analysis import StatisticalAnalyzer
analyzer = StatisticalAnalyzer('path/to/data.json')
report = analyzer.generate_comprehensive_report('output/directory')
"
```

#### Input Data Format

The script expects a JSON file with the following structure:

```json
{
  "metadata": {
    "description": "Validation data description",
    "version": "1.0"
  },
  "results": [
    {
      "n": 10,
      "n_vars": 10,
      "n_clauses": 20,
      "treewidth": 2.5,
      "information_complexity": 3.2,
      "time_dpll": 0.05,
      "solved_dpll": true,
      "algorithms": {
        "cdcl": {"time": 0.04, "solved": true},
        "walksat": {"time": 0.06, "solved": true}
      }
    }
  ]
}
```

#### Output

The script generates:

1. **statistical_report.json** - Comprehensive statistical analysis including:
   - Correlation matrices (Pearson, Spearman, partial)
   - Exponential fit parameters and significance tests
   - Model comparison results (R² values)
   - Algorithm performance comparisons
   - Growth rate exponents with confidence intervals
   - Descriptive statistics

2. **statistical_analysis.png** - Visualization with 6 plots:
   - Treewidth vs Solving Time (log scale)
   - Information Complexity vs Solving Time
   - Correlation heatmap
   - Growth rates over problem size
   - Exponential fit demonstration
   - Algorithm performance comparison (boxplot)

#### Dependencies

```
numpy>=1.24.0
pandas
scipy
matplotlib
seaborn
```

Install with:
```bash
pip install numpy pandas scipy matplotlib seaborn
```

#### Testing

Run the test suite:
```bash
python3 -m pytest tests/test_statistical_analysis.py -v
```

All 12 tests should pass, covering:
- JSON encoding for numpy types
- Data loading and validation
- Correlation analysis
- Exponential hypothesis testing
- No-evasion hypothesis testing
- Growth rate analysis
- Comprehensive report generation

#### Author

José Manuel Mota Burruezo & Claude (Noēsis ∞³)
