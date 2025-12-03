# Quick Start Guide

This guide will help you get the P-NP Computational Dichotomy framework up and running quickly.

## 📄 Official Documentation

For the complete mathematical demonstration and formal proofs, see the official document:

**🔗 [Official Demonstration on Zenodo](https://zenodo.org/records/17315719)**
**🔗 [Permanent DOI Link](https://doi.org/10.5281/zenodo.17315719)**

This repository provides the implementation and practical validation of the concepts described in the official document.

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
- **`formal/`** - Complete formal verification modules:
  - `ComputationalDichotomy.lean` - Computational dichotomy theorem
  - `StructuralCoupling.lean` - Structural coupling lemma (6.24)
  - `InformationComplexity.lean` - Information complexity framework
  - `TreewidthTheory.lean` - Treewidth theory formalization
  - `MainTheorem.lean` - Main P≠NP theorem
  - `VerificationPipeline.lean` - Automated verification pipeline
- **`scripts/formal_verification.sh`** - Complete verification pipeline script
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

### Run Formal Verification

To run the complete formal verification pipeline:

```bash
./scripts/formal_verification.sh
```

This will:
- Build all Lean modules
- Check for incomplete proofs (sorry's)
- Verify the structural coupling lemma
- Verify the main P≠NP theorem
- Generate a verification report in `results/verification/`

## Expected Output

When you run `./run_all_tests.sh`, you should see:

```
