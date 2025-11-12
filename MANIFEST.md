# Repository Manifest

This document provides a comprehensive overview of all files in the P-NP repository.

## 📋 Quick Reference

- **Status**: ✅ All Python components fully tested and working
- **Tests**: 29 unit tests passing
- **Last Updated**: 2025-10-10
- **Python Version**: 3.11+
- **Lean Version**: 4.12.0

## 📂 Directory Structure

### Root Files

| File | Description | Status |
|------|-------------|--------|
| `README.md` | Main project documentation | ✅ Complete |
| `QUICKSTART.md` | Quick start guide | ✅ Complete |
| `CONTRIBUTING.md` | Contribution guidelines | ✅ Complete |
| `MANIFEST.md` | This file - repository overview | ✅ Complete |
| `LICENSE` | MIT License | ✅ Complete |
| `requirements.txt` | Python dependencies | ✅ Complete |
| `run_all_tests.sh` | Comprehensive test script | ✅ Tested |
| `simple_demo.py` | Simple demonstration script | ✅ Tested |
| `.gitignore` | Git ignore rules | ✅ Complete |

### Source Code (`src/`)

| File | Description | Tests | Status |
|------|-------------|-------|--------|
| `computational_dichotomy.py` | Core framework, CNFFormula class | ✅ | ✅ Working |
| `ic_sat.py` | IC-SAT algorithm implementation | ✅ | ✅ Working |
| `gadgets/tseitin_generator.py` | Tseitin formula generator | ✅ | ✅ Working |

### Tests (`tests/`)

| File | Test Count | Description | Status |
|------|-----------|-------------|--------|
| `test_ic_sat.py` | 20 tests | IC-SAT algorithm tests | ✅ Passing |
| `test_tseitin.py` | 9 tests | Tseitin generator tests | ✅ Passing |

**Total**: 29 unit tests, all passing

### Examples (`examples/`)

| File | Description | Status |
|------|-------------|--------|
| `demo_ic_sat.py` | Complete demonstration (7 demos) | ✅ Working |
| `sat/simple_example.cnf` | Sample CNF file (DIMACS format) | ✅ Valid |

### Documentation (`docs/`)

| File | Description | Status |
|------|-------------|--------|
| `DOCUMENTO_OFICIAL.md` | Official demonstration document reference (Zenodo) | ✅ Complete |
| `IC_SAT_IMPLEMENTATION.md` | IC-SAT implementation notes | ✅ Complete |
| `UNIFICACION_COMPLEJIDAD_ESPECTRAL.md` | Spectral complexity unification | ✅ Complete |
| `LEMA_6_24_ACOPLAMIENTO.md` | Lemma 6.24 (Structural Coupling) | ✅ Complete |
| `DUALIDAD_RESOLUCION_INFOCOM.md` | Resolution-InfoCom duality | ✅ Complete |

### Lean Formalization

| File | Description | Status |
|------|-------------|--------|
| `ComputationalDichotomy.lean` | Main formalization | ✅ Valid syntax |
| `Main.lean` | Entry point | ✅ Valid syntax |
| `Principal.lean` | Principal definitions | ✅ Valid syntax |
| `lakefile.lean` | Lake build configuration | ✅ Valid |
| `lean-toolchain` | Lean version specification | ✅ Valid |

### GitHub Configuration (`.github/`)

| File | Description | Status |
|------|-------------|--------|
| `workflows/validate-python.yml` | Python CI/CD | ✅ Updated |
| `workflows/validate-lean.yml` | Lean CI/CD | ✅ Valid |
| `COPILOT_GUIDE.md` | Copilot instructions | ✅ Complete |

## 🧪 Testing Overview

### Unit Tests (pytest)

```bash
pytest tests/ -v
```

**Results**: 29/29 tests passing

**Coverage**:
- ✅ Graph construction (primal, incidence)
- ✅ Treewidth estimation
- ✅ Clause simplification
- ✅ Unit propagation
- ✅ DPLL solver
- ✅ IC-SAT algorithm
- ✅ Tseitin generator
- ✅ Large-scale validation

### Integration Tests

```bash
./run_all_tests.sh
```

**Tests**:
1. ✅ Python dependencies
2. ✅ Unit tests (pytest)
3. ✅ test_ic_sat.py standalone
4. ✅ test_tseitin.py standalone
5. ✅ ic_sat.py module
6. ✅ computational_dichotomy.py module
7. ✅ tseitin_generator.py module
8. ✅ demo_ic_sat.py complete demo

### Manual Verification

```bash
# Simple demo
python3 simple_demo.py

# Complete demo
python3 examples/demo_ic_sat.py
```

## 📦 Dependencies

### Python (requirements.txt)

- `networkx>=3.0` - Graph algorithms and data structures
- `numpy>=1.24.0` - Numerical computing
- `pytest>=7.0.0` - Testing framework

### Lean

- `lean4:4.12.0` - Lean prover
- `mathlib4:v4.12.0` - Mathematical library

## 🎯 Features

### Implemented ✅

- [x] IC-SAT recursive algorithm with depth limits
- [x] Simple DPLL SAT solver (no external dependencies)
- [x] Treewidth estimation (primal and incidence graphs)
- [x] Clause simplification and unit propagation
- [x] Variable prediction heuristics
- [x] Tseitin formula generator over expander graphs
- [x] Large-scale validation framework
- [x] CNF formula class and utilities
- [x] Comprehensive test suite
- [x] Complete documentation

### Formal Verification (Lean)

- [x] Basic definitions (Literal, Clause, CNFFormula)
- [x] Satisfiability definitions
- [x] Treewidth axiomatization
- [x] Structural coupling axiom (Lemma 6.24)
- [x] Dichotomy theorem statement
- [ ] Complete proofs (pending)

## 📊 Code Statistics

| Metric | Count |
|--------|-------|
| Python files | 5 |
| Lean files | 4 |
| Test files | 2 |
| Documentation files | 7 |
| Total lines of Python | ~1500 |
| Total lines of Lean | ~100 |
| Unit tests | 29 |
| Test coverage | High |

## 🚀 Getting Started

See [QUICKSTART.md](QUICKSTART.md) for detailed instructions.

**Quick setup**:
```bash
pip install -r requirements.txt
./run_all_tests.sh
```

## 📝 Version History

### Current (v1.0.0) - 2025-10-10

- ✅ All Python components working
- ✅ 29 unit tests passing
- ✅ Complete documentation
- ✅ Demo scripts functional
- ✅ CI/CD workflows updated

### Key Fixes

1. Added missing `CNFFormula` class
2. Added `generate_low_treewidth_formula` function
3. Created comprehensive test suite
4. Added quick start documentation
5. Updated CI/CD workflows

## 🔗 Related Documents

- [README.md](README.md) - Main documentation
- [QUICKSTART.md](QUICKSTART.md) - Getting started
- [CONTRIBUTING.md](CONTRIBUTING.md) - Contribution guide
- [docs/DOCUMENTO_OFICIAL.md](docs/DOCUMENTO_OFICIAL.md) - Official demonstration document (Zenodo)
- [docs/IC_SAT_IMPLEMENTATION.md](docs/IC_SAT_IMPLEMENTATION.md) - Implementation details

## 👤 Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

Frecuencia de resonancia: 141.7001 Hz

## 📄 License

MIT License - See [LICENSE](LICENSE) file
