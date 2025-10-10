# Changelog

All notable changes to the ICQ P-NP Framework will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2025-10-10

### Added
- **Python Package Structure**: Created `src/icq_pnp/` as importable package
  - `__init__.py` with version info and exports
  - Modular structure for computational_dichotomy and tseitin_generator
  
- **IC-SAT Validation Framework**
  - `ic_sat_validate()` function for automated testing
  - Configurable parameters via argparse (--n, --ratio, --output-dir)
  - CSV output for reproducible results
  - Log-log plotting for treewidth scaling analysis
  
- **Enhanced Tseitin Generator**
  - `generate_margulis_gabber_galil_expander()` for explicit expanders
  - `generate_tseitin_formula()` with configurable parity
  - Support for both satisfiable and unsatisfiable instances
  
- **Test Infrastructure**
  - `tests/test_ic_sat.py` with pytest framework
  - Low treewidth tests (polynomial time expected)
  - High treewidth tests (exponential growth expected)
  - Integration tests for complete framework
  
- **Data Benchmarks**
  - `data/benchmarks/small.cnf` - Low treewidth instance
  - `data/benchmarks/expander.cnf` - High treewidth instance
  
- **CI/CD Enhancements**
  - Pytest integration in Python validation workflow
  - Artifact upload for results and plots
  - Mathlib caching in Lean workflow
  
- **Project Documentation**
  - CHANGELOG.md for version tracking
  - Updated .gitignore for results management
  - Results directory structure with .gitkeep files

### Changed
- Module headers updated to reference Instituto de Conciencia Cuántica (ICQ)
- Python workflow now runs pytest and generates validation results
- Enhanced error handling and type conversion (numpy bool to Python bool)

### Technical Details
- **Dependencies**: networkx, numpy, pytest, matplotlib, pandas
- **Python Version**: 3.10+
- **Lean Version**: 4.10.0
- **Testing**: 10 passing tests (6 IC-SAT + 4 Tseitin)

---

**Author**: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)  
**Frecuencia de resonancia**: 141.7001 Hz  
**Campo**: QCAL ∞³
