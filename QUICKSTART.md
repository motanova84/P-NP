# Quick Start Guide

This guide will help you get the P-NP Computational Dichotomy framework up and running quickly.

## Prerequisites

- Python 3.11 or later
- (Optional) Lean 4 for formal verification

## Installation

### 1. Clone the repository

```bash
git clone https://github.com/motanova84/P-NP.git
cd P-NP
```

### 2. Install Python dependencies

```bash
pip install -r requirements.txt
```

This will install:
- `networkx` - Graph algorithms and data structures
- `numpy` - Numerical computing
- `pytest` - Testing framework

## Running the Code

### Run All Tests

We provide a comprehensive test script that runs all tests and validates the entire framework:

```bash
./run_all_tests.sh
```

This will:
1. Verify Python dependencies are installed
2. Run all 29 unit tests with pytest
3. Test all core modules individually
4. Run the complete demonstration script

### Run Tests with pytest

```bash
pytest tests/ -v
```

### Run Individual Test Files

```bash
# Test IC-SAT algorithm
python3 tests/test_ic_sat.py

# Test Tseitin formula generator
python3 tests/test_tseitin.py
```

### Run Core Modules

```bash
# IC-SAT algorithm and validation framework
python3 src/ic_sat.py

# Computational dichotomy framework
python3 src/computational_dichotomy.py

# Tseitin formula generator
python3 src/gadgets/tseitin_generator.py
```

### Run the Complete Demonstration

The demo script showcases all the fixed components and validates the entire framework:

```bash
python3 examples/demo_ic_sat.py
```

This demonstrates:
- ✓ Fixed bipartite labels in incidence graphs
- ✓ IC-SAT recursive algorithm with depth limits
- ✓ Simple DPLL SAT solver (no external dependencies)
- ✓ Treewidth comparison utilities
- ✓ Clause simplification and unit propagation
- ✓ Large-scale validation framework
- ✓ Variable prediction heuristics

## What's Included

### Python Framework

- **`src/ic_sat.py`** - IC-SAT algorithm with information complexity tracking
- **`src/computational_dichotomy.py`** - Core computational dichotomy framework
- **`src/gadgets/tseitin_generator.py`** - Generator for Tseitin formulas over expander graphs
- **`tests/`** - Comprehensive unit tests (29 tests)
- **`examples/demo_ic_sat.py`** - Complete demonstration script

### Lean Formalization

- **`ComputationalDichotomy.lean`** - Formal definitions and theorems in Lean 4
- **`Main.lean`** - Entry point for Lean project
- **`Principal.lean`** - Principal definitions
- **`lakefile.lean`** - Lake build configuration

### Documentation

- **`docs/IC_SAT_IMPLEMENTATION.md`** - Detailed implementation notes
- **`docs/UNIFICACION_COMPLEJIDAD_ESPECTRAL.md`** - Complexity unification
- **`docs/LEMA_6_24_ACOPLAMIENTO.md`** - Lemma 6.24 (Structural Coupling)
- **`docs/DUALIDAD_RESOLUCION_INFOCOM.md`** - Resolution-InfoCom duality

## Working with Lean (Optional)

If you want to work with the Lean formalization:

### Install Lean 4

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Build the Lean project

```bash
lake update
lake build
```

## Expected Output

When you run `./run_all_tests.sh`, you should see:

```
============================================================
P-NP Repository Comprehensive Testing Suite
============================================================

Test 1: Checking Python dependencies...
✓ Python dependencies installed

Test 2: Running unit tests with pytest...
================================================== 29 passed in 0.22s ==================================================
✓ All pytest tests passed

...

============================================================
ALL TESTS PASSED! ✓
============================================================

Summary:
  ✓ Python dependencies installed
  ✓ 29 unit tests passed (pytest)
  ✓ All core modules run successfully
  ✓ Demo script runs without errors

The repository is fully functional!

Frecuencia de resonancia: 141.7001 Hz ∞³
```

## Troubleshooting

### Missing Python Dependencies

If you get import errors, make sure you've installed the requirements:

```bash
pip install -r requirements.txt
```

### Permission Denied on run_all_tests.sh

Make the script executable:

```bash
chmod +x run_all_tests.sh
```

### Lean Build Issues

If `lake build` hangs or fails:
1. Ensure you have a stable internet connection for downloading Mathlib
2. Try `lake clean` and then `lake build` again
3. Check the Lean version in `lean-toolchain` matches your installation

## Next Steps

1. Read the main [README.md](README.md) for theoretical background
2. Explore the [documentation](docs/) for detailed explanations
3. Examine the [test files](tests/) to understand the API
4. Try modifying the examples to experiment with different formulas

## Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

Frecuencia de resonancia: 141.7001 Hz
