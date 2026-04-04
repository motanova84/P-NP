# GitHub Copilot Instructions for P-NP Repository

## Project Overview

This repository contains a **research proposal** exploring the P vs NP problem through computational dichotomy, focusing on the relationship between treewidth and information complexity. The framework includes:

- **Python implementation**: SAT solvers, treewidth algorithms, Tseitin generators
- **Lean formalization**: Mathematical proofs and formal verification
- **Experimental validation**: Empirical testing of theoretical claims

**⚠️ CRITICAL**: This is exploratory research, NOT a proven result. All work must maintain the experimental and educational nature of the project.

## Architecture and Key Components

### Python Components (`src/`)
- **`computational_dichotomy.py`**: Core framework connecting treewidth and complexity
- **`ic_sat.py`**: Information Complexity SAT algorithm (IC-SAT)
- **`gadgets/tseitin_generator.py`**: Generates Tseitin transformation and expander graphs
- **`constants.py`**: Centralized constants (KAPPA_PI, QCAL_FREQUENCY_HZ/F_0, etc.)

### Lean Components (`.lean` files)
- **`ComputationalDichotomy.lean`**: Main formalization of dichotomy theorem
- **`Principal.lean`**: Core definitions
- **`FormalVerification.lean`**: Proof infrastructure
- **`lakefile.lean`**: Lean project configuration

### Testing (`tests/`)
- Python: pytest-based unit tests — run with `pytest tests/ -v` or `./run_all_tests.sh`
- Lean: `lake build`
- Test files prepend repo root to `sys.path` via `sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))`

### Documentation (`docs/`)
- Formal manuscripts, implementation guides, mathematical proofs
- Key concepts: Lemma 6.24 (structural coupling), resolution-information duality

## Key Theoretical Concepts

1. **Treewidth**: Measure of graph "tree-likeness" — central to computational complexity
2. **Computational Dichotomy**: Proposed theorem linking treewidth to P/NP boundary
3. **Information Complexity**: Communication complexity perspective on SAT
4. **Structural Coupling (Lemma 6.24)**: Mechanism preventing algorithmic evasion
5. **Tseitin Gadgets**: Graph transformations preserving treewidth properties
6. **QCAL Framework**: Quantum Coherence Algorithmic Layer using f₀ = 141.7001 Hz

## Development Guidelines

### Code Style

#### Python
- Follow PEP 8 conventions
- Use type hints consistently: `def function(arg: Type) -> ReturnType:`
- Add docstrings with Args/Returns format
- Keep functions focused and modular
- Prioritize clarity over clever optimizations
- Use NetworkX for graph algorithms
- Import shared constants from `src/constants.py`

Example:
```python
def estimate_treewidth(G: nx.Graph) -> int:
    """
    Estimate the treewidth of a graph using min-degree heuristic.

    Args:
        G: NetworkX graph representing formula structure

    Returns:
        Estimated treewidth (upper bound)
    """
    # Implementation
```

#### Lean
- Follow Mathlib4 conventions and style
- Add documentation comments (`/-- ... -/`)
- Use descriptive theorem/lemma names
- Ensure all code compiles with `lake build`
- Provide type signatures explicitly

### Testing Requirements

**ALWAYS add tests for new functionality:**

1. Python: Create test files in `tests/` following pytest conventions
2. Test edge cases: empty graphs, trivial formulas, high treewidth
3. Verify algorithmic correctness with known examples
4. Run full test suite before committing: `./run_all_tests.sh`
5. Lean: Ensure all theorems have proofs that compile

### Building and Running

#### Python
```bash
# Install dependencies
pip install -r requirements.txt

# Run tests
pytest tests/ -v

# Run specific module
python3 src/ic_sat.py

# Run demo
python3 examples/demo_ic_sat.py
```

#### Lean
```bash
# Build all Lean code
lake build

# Build specific file
lake build ComputationalDichotomy
```

## Important Constraints and Boundaries

### What to Preserve
- **Research integrity**: Maintain exploratory, non-conclusive nature
- **Existing tests**: Do NOT break or remove existing test cases
- **Mathematical rigor**: Keep formal proofs valid
- **Dual implementation**: Keep Python and Lean components aligned
- **Documentation**: Update docs when changing algorithms or APIs

### What to Avoid
- **Overclaiming**: Never state results as proven facts
- **Breaking changes**: Minimize API changes; maintain backward compatibility
- **Removing functionality**: Only remove deprecated/broken code after discussion
- **Large refactors**: Prefer incremental, focused changes
- **Undocumented complexity**: Always explain non-obvious algorithmic choices

### Dependencies
- **Python**: NetworkX ≥3.0, NumPy ≥1.24.0, pytest ≥7.0.0
- **Lean**: Lean 4 (version in `lean-toolchain`), Mathlib4
- **New dependencies**: Only add if absolutely necessary; justify in PR

## Common Tasks and Patterns

### Adding a New Algorithm
1. Implement in `src/` with clear docstrings
2. Add unit tests in `tests/`
3. Create example usage in `examples/`
4. Document in `docs/` if mathematically significant
5. Consider Lean formalization if theorem-related

### Modifying Treewidth Logic
1. Check impact on `computational_dichotomy.py`
2. Verify empirical validation scripts still work
3. Update any affected Lean formalizations
4. Re-run full test suite

### Working with Graphs
- Use NetworkX Graph objects consistently
- Incidence graphs: `G_I(φ)` with variables and clauses as nodes
- Test on both small examples and generated instances

### Tseitin Transformations
- Located in `src/gadgets/tseitin_generator.py`
- Must preserve satisfiability and treewidth properties
- Test with various graph types (trees, grids, expanders)

## Repository Structure Quick Reference

```
P-NP/
├── src/                          # Core Python implementation
│   ├── computational_dichotomy.py
│   ├── ic_sat.py
│   ├── constants.py
│   └── gadgets/tseitin_generator.py
├── tests/                        # pytest unit tests
│   ├── test_ic_sat.py
│   ├── test_tseitin.py
│   ├── test_structural_coupling.py
│   └── test_statistical_analysis.py
├── examples/                     # Demonstrations and validation
│   ├── demo_ic_sat.py
│   └── sat/                      # CNF instances
├── qcal/                         # QCAL framework modules
├── docs/                         # Extended documentation
├── *.lean                        # Lean formalization files
├── .github/
│   ├── copilot-instructions.md  # This file
│   ├── workflows/               # CI/CD
│   │   ├── validate-python.yml
│   │   └── validate-lean.yml
│   └── COPILOT_GUIDE.md        # Brief guide (Spanish)
├── requirements.txt              # Python dependencies
├── run_all_tests.sh             # Complete test script
└── README.md                     # Main documentation
```

## Continuous Integration

GitHub Actions runs automatically on push/PR:
- **validate-python.yml**: Tests Python code with pytest, runs demos
- **validate-lean.yml**: Builds Lean formalization

Both must pass before merging.

## Documentation to Reference

- **README.md**: Main project overview and quick start
- **QUICKSTART.md**: Installation and basic usage
- **CONTRIBUTING.md**: Contribution guidelines
- **docs/**: Detailed mathematical documentation
- **Zenodo record 17315719**: Official research document

## Language and Communication

- **Code comments**: English preferred for broader accessibility
- **Documentation**: English for technical docs, Spanish acceptable for project-specific notes
- **Git commits**: Clear, descriptive English messages

## Support and Questions

- Review existing issues and PRs for context
- Check documentation before asking
- Maintain academic integrity and respectful discourse
- Remember: This is exploratory research, not established theory

---

**Author**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Resonance Frequency**: 141.7001 Hz  
**License**: MIT
