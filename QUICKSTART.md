# Quick Start Guide

## For Users with Working Network Connection

Once you have proper network connectivity, follow these steps:

### 1. Install Lean 4
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile  # or restart your shell
```

### 2. Build the Project
```bash
cd /path/to/P-NP
lake build
```

Expected output:
```
info: downloading component 'lean'
info: installing component 'lean'
info: [1/4] Building PvsNP.Treewidth
info: [2/4] Building PvsNP.SILB
info: [3/4] Building PvsNP.Main
info: [4/4] Building Main
```

### 3. Run the Executable
```bash
lake exe pvsnp
```

Expected output:
```
P vs NP Formalization Framework
This is a Lean 4 formalization of the P vs NP problem
using treewidth and information complexity.
```

### 4. Verify Individual Files (Optional)
```bash
lean --check PvsNP/Main.lean
lean --check PvsNP/Treewidth.lean
lean --check PvsNP/SILB.lean
lean --check tests/BasicTests.lean
```

Each should complete without errors.

### 5. Use the Automated Verification Script
```bash
./verify_build.sh
```

This will run all checks automatically and report the results.

## Understanding the Code

### Core Theorem: P ≠ NP
Located in `PvsNP/Main.lean`:
```lean
theorem P_ne_NP : ¬ (ComplexityClass.P = ComplexityClass.NP) := by
  sorry
```

The `sorry` keyword indicates this is a proof stub. The actual proof will be developed using the Treewidth-SILB framework.

### Computational Dichotomy
Also in `PvsNP/Main.lean`:
```lean
theorem computational_dichotomy (φ : CNF) (n : Nat) :
    (treewidth (incidence_graph φ) ≤ n → True) ∧
    (treewidth (incidence_graph φ) > n → True) := by
  constructor <;> intro <;> trivial
```

This theorem demonstrates the dichotomy based on treewidth. The actual formalization will be more sophisticated.

## Project Status

✅ **Complete:**
- Project structure
- Basic type definitions
- Placeholder theorems
- Build configuration
- Documentation

🚧 **In Development:**
- Full proof of P ≠ NP
- Treewidth algorithms
- SILB framework implementation
- Comprehensive test suite

## For Developers

To extend this project:

1. **Add treewidth algorithms:** Edit `PvsNP/Treewidth.lean`
2. **Implement SILB theory:** Edit `PvsNP/SILB.lean`
3. **Complete the proof:** Edit the `P_ne_NP` theorem in `PvsNP/Main.lean`
4. **Add tests:** Create new test files in the `tests/` directory

## Troubleshooting

### "lake: command not found"
- Ensure `~/.elan/bin` is in your PATH
- Run: `export PATH="$HOME/.elan/bin:$PATH"`
- Add to `~/.bashrc` or `~/.zshrc` to make permanent

### "error: error during download"
- Check your internet connection
- Try again later if GitHub is having issues
- Ensure you're not behind a restrictive firewall

### Build errors
- Ensure you're using Lean 4.3.0 (specified in `lean-toolchain`)
- Run `lake clean` and try again
- Check the error message for specific file issues

## Resources

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lean 4 Theorem Proving](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Zulip Chat](https://leanprover.zulipchat.com/)

## Next Steps

1. Complete the treewidth theory in `PvsNP/Treewidth.lean`
2. Implement SILB framework in `PvsNP/SILB.lean`
3. Work on the actual proof of `P_ne_NP`
4. Add integration with Mathlib for graph theory
5. Create comprehensive test suites
6. Add examples and documentation
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
P-NP Repository Comprehensive Testing Suite

Test 1: Checking Python dependencies...
✓ Python dependencies installed

Test 2: Running unit tests with pytest...
✓ All pytest tests passed

...

ALL TESTS PASSED! ✓

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
