# GAP 6: Empirical Validation

## Overview

This document describes the empirical validation framework for testing theoretical bounds on real SAT instances.

## Requirements

### Dataset Requirements

1. **SAT Competition Instances** (n > 10⁶)
   - Industrial benchmarks
   - Application instances
   - Crafted hard instances

2. **Random 3-SAT** (m/n ≈ 4.267)
   - Phase transition region
   - Various sizes: 100, 500, 1000, 5000 variables
   - 100+ instances per size

3. **NP-Complete Reductions**
   - Clique to SAT
   - Vertex Cover to SAT
   - 3-Coloring to SAT

### Metrics to Measure

1. **Treewidth Distribution**
   - Mean, std, min, max per instance size
   - Correlation with density
   - Growth rate with n

2. **IC-SAT Failure Cases**
   - Instances where IC bound doesn't apply
   - Patterns in failure modes
   - Structural differences from theory

3. **Solver Comparison**
   - Time vs theoretical bound
   - Which solvers approach bound
   - Gap between practice and theory

## Implementation

### Treewidth Estimation

Located in `python_validation/empirical_validation.py`:

```python
class TreewidthEstimator:
    """
    Estimates treewidth using min-degree heuristic.
    Note: Exact treewidth is NP-hard.
    """
    
    @staticmethod
    def estimate_treewidth(instance: SATInstance) -> TreewidthMetrics:
        # Returns estimated treewidth, nodes, edges, time
```

**Limitations**:
- Heuristic approximation only
- May underestimate true treewidth
- Exact computation infeasible for large instances

### Information Complexity Bounds

```python
class InformationComplexityEstimator:
    """Estimates IC lower bounds"""
    
    @staticmethod
    def estimate_ic_lower_bound(instance: SATInstance, alpha: float) -> float:
        """
        Current: α ≈ 0.006
        Target: α ≥ 0.1
        """
        tw_metrics = TreewidthEstimator.estimate_treewidth(instance)
        k = tw_metrics.estimated_treewidth
        return alpha * k
```

### Solver Benchmarking

Located in `python_validation/solver_comparison.py`:

```python
class SATSolverBenchmark:
    """Benchmark against real solvers"""
    
    def run_solver(self, solver_name: str, instance: SATInstance, 
                   timeout: float) -> SolverResult:
        # Returns satisfiability, time, decisions, conflicts
    
    def compare_with_theory(self, n_vars: int, density: float,
                           n_instances: int) -> Dict:
        # Returns comparison between theory and practice
```

**Supported Solvers**:
- CryptoMiniSat 5
- Kissat
- MiniSat
- (others if installed)

## Usage

### Running Validation

```bash
cd python_validation

# Install dependencies
pip install -r requirements.txt

# Run treewidth and IC validation
python empirical_validation.py

# Compare with solvers (requires solvers installed)
python solver_comparison.py
```

### Sample Output

```
==================================================================
EMPIRICAL VALIDATION REPORT - P-NP Framework
==================================================================

TREEWIDTH STATISTICS:
------------------------------------------------------------------
Variables    Mean TW      Std TW       Min TW       Max TW      
------------------------------------------------------------------
100          5.23         1.45         3            8           
500          7.89         2.01         5            12          
1000         9.12         2.34         6            14          

INFORMATION COMPLEXITY BOUNDS:
------------------------------------------------------------------
Variables    Current α=0.006  Target α=0.1     Improvement
------------------------------------------------------------------
100          0.0314           0.5230           16.67x      
500          0.0473           0.7890           16.67x      
1000         0.0547           0.9120           16.67x      
==================================================================
```

## Test Scenarios

### Scenario 1: Random 3-SAT at Phase Transition

**Setup**: m/n = 4.267, various n  
**Expected**: High treewidth, hard for solvers  
**Validates**: IC bounds on unstructured instances

### Scenario 2: Industrial Benchmarks

**Setup**: Real-world SAT instances  
**Expected**: Lower treewidth, easier than random  
**Validates**: Gap between worst-case and average-case

### Scenario 3: Structured Reductions

**Setup**: Graph problems reduced to SAT  
**Expected**: Preserves structure, predictable treewidth  
**Validates**: Tightness of reduction

## Expected Results

### Hypothesis 1: Treewidth Grows
- Random 3-SAT: tw ≈ Θ(log n)
- Structured: tw ≈ Θ(√n) or higher
- Validates need for ω(1) assumption

### Hypothesis 2: Solvers Vary
- Average case: Solvers much faster than bound
- Worst case: Some instances approach bound
- Validates practical vs theoretical gap

### Hypothesis 3: α Improvement Needed
- Current α = 0.006 gives trivial bounds
- Target α = 0.1 gives meaningful bounds
- Validates importance of GAP 2

## Challenges

### 1. Exact Treewidth
- NP-hard to compute
- Heuristics may underestimate
- Need multiple methods for validation

### 2. Solver Availability
- Not all solvers easily installed
- Different versions, configurations
- Results may vary by platform

### 3. Instance Generation
- Random instances may not capture structure
- Real benchmarks may be too easy
- Need balanced test suite

### 4. Statistical Significance
- Need many instances per size
- Variance can be high
- Outliers may be important

## Future Work

### Short Term
1. Implement exact treewidth for small instances
2. Add more solvers to benchmark
3. Generate structured hard instances

### Medium Term
1. Test on SAT Competition benchmarks
2. Analyze correlation between metrics
3. Identify failure modes

### Long Term
1. Build comprehensive benchmark suite
2. Automate continuous testing
3. Publish empirical findings

## Validation Checklist

- [ ] Test on n = [100, 500, 1000, 5000, 10000]
- [ ] Compare 3 different treewidth heuristics
- [ ] Benchmark against 3+ SAT solvers
- [ ] Generate 100+ instances per configuration
- [ ] Analyze statistical significance
- [ ] Document failure cases
- [ ] Create visualization of results
- [ ] Compare with SAT Competition data

## References

- [SAT Competition](http://www.satcompetition.org/)
- [SATLIB Benchmarks](https://www.cs.ubc.ca/~hoos/SATLIB/)
- [Treewidth Estimation](https://github.com/holgerdell/PACE-treewidth-solvers)
- [MiniSat](http://minisat.se/)
- [CryptoMiniSat](https://github.com/msoos/cryptominisat)
