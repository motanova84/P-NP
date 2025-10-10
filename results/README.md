# Results Directory

This directory contains output from the IC-SAT validation framework.

## Structure

```
results/
├── .gitkeep                      # Preserves directory in git
├── ic_sat_results.csv            # Numerical validation results
└── plots/
    ├── .gitkeep                  # Preserves directory in git
    └── treewidth_scaling.png     # Log-log plot of treewidth vs problem size
```

## Generated Files

### `ic_sat_results.csv`

Contains validation results with columns:
- `n`: Problem size (number of variables)
- `treewidth`: Approximate treewidth of the incidence graph
- `coherence`: Coherence measure (log(n) / (tw + 1))
- `solved`: Boolean indicating tractability (tw ≤ O(log n))

### `plots/treewidth_scaling.png`

Log-log plot showing:
- Blue line with circles: Observed treewidth for low-treewidth formulas
- Red dashed line: Theoretical O(log n) bound
- Demonstrates that low treewidth formulas remain tractable as size increases

## Generating Results

Run the IC-SAT validation framework:

```bash
# Default parameters
python -m src.icq_pnp.computational_dichotomy

# Custom problem sizes
python -m src.icq_pnp.computational_dichotomy --n 100 200 300 500 1000

# Custom output directory
python -m src.icq_pnp.computational_dichotomy --output-dir my_results
```

## CI/CD Integration

The GitHub Actions workflow automatically:
1. Runs the validation framework
2. Generates results and plots
3. Uploads as artifacts for download

See `.github/workflows/validate-python.yml` for details.

---

**Note**: Generated files (CSV, PNG) are excluded from git via `.gitignore` 
but the directory structure is preserved with `.gitkeep` files.
