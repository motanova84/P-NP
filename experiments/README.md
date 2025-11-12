# Experiments Directory

This directory contains experimental validation scripts for the P≠NP framework.

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
