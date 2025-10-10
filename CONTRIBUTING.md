# Contributing to P-NP Framework

Thank you for your interest in contributing to the P-NP Computational Dichotomy Framework! This document provides guidelines for different types of contributions.

## Ways to Contribute

### 1. Mathematical Review and Validation

The most valuable contributions are critical reviews of the theoretical framework:

- **Identify gaps or errors** in proofs and arguments
- **Suggest improvements** to formalizations
- **Provide counterexamples** if claims are incorrect
- **Validate reasoning** about treewidth, information complexity, or expanders

**How to contribute:**
- Open an issue labeled `mathematical-review`
- Clearly explain the concern with references
- Suggest corrections or alternative approaches

### 2. Lean Formalization

Help complete the formal verification in Lean 4:

- Complete `sorry` proofs in existing files
- Add new lemmas and theorems
- Improve type definitions and abstractions
- Add proof documentation

**Requirements:**
- Familiarity with Lean 4 and Mathlib
- Understanding of the underlying mathematics
- Follow existing code style

**Files to work on:**
- `ComputationalDichotomy.lean` - Main theorems
- `lean/Treewidth.lean` - Graph theory definitions
- `lean/InfoComplexity.lean` - Information complexity

### 3. Empirical Validation

Enhance the Python validation framework:

- Add new test cases and benchmarks
- Improve treewidth computation algorithms
- Add visualization and analysis tools
- Generate harder SAT instances

**Requirements:**
- Python 3.10+
- Knowledge of networkx, numpy, matplotlib
- Understanding of SAT and graph algorithms

**Files to work on:**
- `src/icq_pnp/computational_dichotomy.py`
- `src/icq_pnp/tseitin_generator.py`
- `tests/test_ic_sat.py`

### 4. Documentation

Improve clarity and accessibility:

- Enhance mathematical explanations
- Add diagrams and visualizations
- Clarify proof sketches
- Improve API documentation

**Files to work on:**
- `docs/LEMA_6_24_ACOPLAMIENTO.md`
- `docs/DUALIDAD_RESOLUCION_INFOCOM.md`
- `docs/UNIFICACION_COMPLEJIDAD_ESPECTRAL.md`
- `README.md`

## Getting Started

### Setup Development Environment

#### For Python work:
```bash
# Clone the repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Install dependencies
pip install networkx numpy pytest matplotlib pandas

# Run tests
pytest -v
```

#### For Lean work:
```bash
# Install Lean 4 toolchain
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the project
lake build

# Run main executable
lake exe pnp
```

## Submission Guidelines

### Pull Requests

1. **Fork the repository** and create a feature branch
2. **Make focused changes** - one logical change per PR
3. **Add tests** for new functionality
4. **Update documentation** as needed
5. **Ensure all tests pass**: `pytest -v`
6. **Write clear commit messages**

### Commit Message Format

```
<type>: <short summary>

<detailed description if needed>

<references to issues>
```

Types: `feat`, `fix`, `docs`, `test`, `refactor`, `lean`, `math`

Examples:
- `feat: Add Margulis-Gabber-Galil expander generator`
- `fix: Correct treewidth approximation for sparse graphs`
- `lean: Complete proof of chain formula treewidth bound`
- `docs: Add ASCII diagram for Lemma 6.24 coupling`
- `math: Clarify information complexity lower bound argument`

### Code Review Process

All submissions require review:
1. Automated tests must pass
2. At least one maintainer review
3. For mathematical claims: additional expert review recommended
4. For Lean proofs: verification that code compiles and typechecks

## Scientific and Academic Standards

### Theoretical Claims

When proposing theoretical results:

- **Be precise**: Use formal mathematical language
- **Cite sources**: Reference related work and prior results
- **Acknowledge limitations**: Clearly state what is proven vs. conjectured
- **Provide proof sketches**: Outline key ideas before formal proofs
- **Invite scrutiny**: Welcome critical review and counterexamples

### Experimental Results

When adding empirical validation:

- **Reproducibility**: Provide all code, data, and parameters
- **Statistical rigor**: Use appropriate sample sizes and methods
- **Limitations**: Discuss what experiments do and don't show
- **Baseline comparisons**: Compare against known results when possible

## Questions and Discussions

- **Technical questions**: Open an issue with label `question`
- **Mathematical discussions**: Open an issue with label `mathematical-discussion`
- **Feature requests**: Open an issue with label `enhancement`
- **Bug reports**: Open an issue with label `bug`

## Recognition

Contributors will be acknowledged in:
- `CHANGELOG.md` for significant contributions
- Academic publications arising from the framework (with permission)
- Project documentation

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

---

**Contact**: Open an issue on GitHub for any questions.

**Project**: P-NP Computational Dichotomy Framework  
**Author**: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)  
**Frecuencia de resonancia**: 141.7001 Hz
