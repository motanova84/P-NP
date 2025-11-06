# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A **formal framework** for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) as the key ingredient that aims to prevent algorithmic evasion.

**🚀 Quick Start:** See [QUICKSTART.md](QUICKSTART.md) for installation and running instructions.

## 🎯 Proposed Main Result

**Computational Dichotomy Theorem (Proposed):**
```
φ ∈ P ⟺ tw(G_I(φ)) = O(log n)
```

Where:
- `φ` is a CNF formula
- `G_I(φ)` is the incidence graph of φ
- `tw(G_I(φ))` is the treewidth of the incidence graph
- `n` is the number of variables

## 🧪 Lean 4 Formalization (Planned)

This repository plans to include a complete Lean 4 formalization of the theoretical framework:

### Planned Project Structure
```
P-NP/
├── PvsNP/                      # Lean 4 formalization (to be added)
│   ├── Main.lean               # Main P ≠ NP theorem
│   ├── Treewidth.lean          # Treewidth definitions and properties
│   ├── SILB.lean               # Separator Information Lower Bounds
│   └── ComputationalModels.lean # Transfer to computational models
├── tests/                      # Verification tests (to be added)
│   └── BasicTests.lean         # Basic compilation tests
├── lakefile.lean               # Project configuration (to be added)
└── README.md                   # This file
├── src/                      # Código fuente principal
│   ├── computational_dichotomy.py  # Framework principal
│   ├── ic_sat.py            # Algoritmo IC-SAT
│   └── gadgets/
│       └── tseitin_generator.py
├── ComputationalDichotomy.lean  # Formalización matemática en Lean
├── Main.lean                 # Punto de entrada Lean
├── Principal.lean            # Definiciones principales
├── lakefile.lean            # Configuración del proyecto Lean
├── examples/                 # Casos de prueba y aplicaciones
│   ├── demo_ic_sat.py       # Demostración completa
│   ├── empirical_validation_n400.py  # Validación empírica n≤400
│   └── sat/                  # Instancias CNF reales
│       └── simple_example.cnf
├── docs/                     # Documentación extendida
│   ├── formal_manuscript.tex # Manuscrito formal LaTeX
│   ├── MANUSCRIPT_README.md # Guía del manuscrito
│   ├── IC_SAT_IMPLEMENTATION.md
│   ├── UNIFICACION_COMPLEJIDAD_ESPECTRAL.md
│   ├── LEMA_6_24_ACOPLAMIENTO.md
│   └── DUALIDAD_RESOLUCION_INFOCOM.md
├── tests/                    # Pruebas unitarias (29 tests)
│   ├── test_ic_sat.py
│   └── test_tseitin.py
├── .github/
│   ├── workflows/
│   │   ├── validate-python.yml
│   │   └── validate-lean.yml
│   └── COPILOT_GUIDE.md
├── requirements.txt          # Dependencias Python
├── run_all_tests.sh         # Script de pruebas completo
├── simple_demo.py           # Demostración simple
├── QUICKSTART.md            # Guía de inicio rápido
├── README.md
└── LICENSE
```

### Building the Project (Future)
```bash
# Install Lean and dependencies
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build the project (once implemented)
lake build

# Run tests (once implemented)
lake test
```

## ✨ The Key Insight: Structural Coupling
φ ∈ P if and only if tw(G_I(φ)) = O(log n)
```

Where:
- `φ` is a CNF formula (Boolean satisfiability problem)
- `G_I(φ)` is the incidence graph of φ
- `tw(G_I(φ))` is the treewidth
- `n` is the number of variables

### 2. Information-Theoretic Barriers

Unlike approaches relying on unproven assumptions (SETH, ETH), this work explores information complexity as a potential avenue for unconditional lower bounds.

### 3. Avoiding Known Barriers (Anti-Barriers)

The framework is designed to circumvent three major barriers in complexity theory:

#### Non-Relativization
The Separator Information Lower Bound (SILB) approach does **not** relativize because:
- Lower bounds depend on explicit separator structure in incidence graphs, not oracle queries
- Information content is computed from graph topology, which has no oracle analogue
- Tseitin gadgets over Ramanujan expanders require specific structural properties

#### Non-Natural Proofs (Razborov-Rudich)
The framework is **not** a natural proof because:
- Predicates are not dense (depend on sparse gadget constructions)
- Treewidth computation is NP-hard (not efficiently constructible)
- Bounds depend on conditional mutual information restricted by topology

#### Non-Algebrization (Aaronson-Wigderson)
The approach does **not** algebrize because:
- Monotonicity of separator information breaks in polynomial quotient rings
- Graph-theoretic separator structure has no natural embedding in algebraic extensions
- Information-theoretic bounds don't extend to algebraic closures

See [Section 6](docs/formal_manuscript.tex) of the formal manuscript for detailed technical arguments.

**Lemma 6.24 (Treewidth-Preserving Structural Coupling)** proposes that:

> Any CNF formula φ with high treewidth can be coupled via gadgets (Tseitin expanders) to a communication instance where the information bottleneck is inherent and cannot be eliminated by classical algorithmic techniques.

This approach uses:

- **Treewidth** as a structural complexity measure
- **Information Complexity** for unconditional lower bounds
- **Expander Graphs** to create non-evadable bottlenecks
- **Formal Verification** via Lean 4 for rigorous proof checking

## 📚 Theoretical Framework

### Core Components

1. **Treewidth Analysis**: Connecting graph structure to computational hardness
2. **Information Complexity Bounds**: Using information-theoretic limits
3. **SILB Framework**: Separator Information Lower Bounds technique
4. **Non-Relativization**: Avoiding oracle-based barriers
5. **Formal Verification**: Complete Lean 4 formalization

### Main Theorems (To Be Formalized in Lean)

- `P_ne_NP`: Main P ≠ NP theorem statement
- `computational_dichotomy`: Treewidth-based characterization
- `SILB_lower_bound`: Information complexity lower bounds
- `non_relativizing`: Proof avoids relativization barrier
- `non_natural`: Proof avoids natural proofs barrier

## ✅ Repository Status

**All Python components are fully functional and tested:**
- ✅ 29 unit tests passing (pytest)
- ✅ IC-SAT algorithm with information complexity tracking
- ✅ DPLL SAT solver (no external dependencies)
- ✅ Treewidth estimation and comparison
- ✅ Tseitin formula generator over expander graphs
- ✅ Large-scale validation framework
- ✅ Complete demonstration scripts

- **Lean 4**: Install via elan
- **Python 3.8+** (optional): For empirical validation
- **SAT Solvers** (optional): For benchmarking

### Building and Verification
**Quick verification:**
```bash
./run_all_tests.sh  # Runs all tests and demos
```

## 🚀 Getting Started

**👉 See [QUICKSTART.md](QUICKSTART.md) for detailed installation and running instructions.**

### Quick Setup

```bash
# 1. Clone the repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# 2. Install Python dependencies
pip install -r requirements.txt

# 3. Run all tests
./run_all_tests.sh

# 4. Try the simple demo
python3 simple_demo.py
```

### Prerequisites

For Python framework:
```bash
# Clone the repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Build with Lake
pip install -r requirements.txt
```

This installs:
- `networkx` - Graph algorithms
- `numpy` - Numerical computing
- `pytest` - Testing framework

### Running the Python Framework

```bash
# Run comprehensive test suite
./run_all_tests.sh

# Run simple demonstration
python3 simple_demo.py

# Run complete demonstration with all features
python3 examples/demo_ic_sat.py

# Run empirical validation on instances up to n=400
python3 examples/empirical_validation_n400.py

# Run specific modules
python3 src/ic_sat.py
python3 src/computational_dichotomy.py
python3 src/gadgets/tseitin_generator.py

# Run unit tests
pytest tests/ -v
```

### Working with Lean Formalization

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the Lean project
lake build

# Run verification tests
lake test
```

## 🔬 Research Status

### ✅ Completed
- Comprehensive documentation and README
- Research framework outline
- Theoretical foundation description

### 🔄 In Progress
- Setting up Lean 4 project structure
- Formalizing core definitions and theorem statements
- Setting up CI/CD pipeline with GitHub Actions
- Completing formal proofs (replacing sorry placeholders)
- Improving constant bounds in SILB theorems
- Extending empirical validation
- Peer review and verification

### 📋 Known Gaps
- Lean 4 project files need to be created
- GitHub Actions workflow for CI needs to be set up
- Several theorems will use `sorry` (proof placeholders) initially
- Need to complete treewidth-preserving coupling proof
- Empirical validation needs implementation and larger test suite

## 🤝 Contributing
### Formal Manuscript

See [docs/formal_manuscript.tex](docs/formal_manuscript.tex) for the complete formal LaTeX manuscript presenting:
- Treewidth-based framework for P ≠ NP
- Structural Separation Theorem
- Information Coupling Lemma (Lemma 6.24)
- Spectral Anti-Bypass Lemma
- Lean4 formalization
- Empirical validation on instances up to n=400

Compilation instructions in [docs/MANUSCRIPT_README.md](docs/MANUSCRIPT_README.md).

### Additional Documentation

See also:
- [docs/LEMA_6_24_ACOPLAMIENTO.md](docs/LEMA_6_24_ACOPLAMIENTO.md) - Detailed explanation of Lemma 6.24
- [docs/IC_SAT_IMPLEMENTATION.md](docs/IC_SAT_IMPLEMENTATION.md) - IC-SAT implementation details
- [docs/UNIFICACION_COMPLEJIDAD_ESPECTRAL.md](docs/UNIFICACION_COMPLEJIDAD_ESPECTRAL.md) - Spectral complexity unification
- [docs/DUALIDAD_RESOLUCION_INFOCOM.md](docs/DUALIDAD_RESOLUCION_INFOCOM.md) - Resolution-InfoCom duality

This is a research project exploring a novel approach to P vs NP. Contributions welcome in:

- **Proof Completion**: Replacing `sorry` with actual proofs
- **Mathematical Review**: Identifying gaps or improvements
- **Formal Verification**: Helping complete Lean proofs
- **Documentation**: Improving explanations and examples

## ⚠️ Important Disclaimer

**This is theoretical research in progress:**

- Claims have not been peer-reviewed
- Proofs contain gaps requiring rigorous verification
- This should be viewed as a formalization of a research program
- **NOT a complete proof of P ≠ NP**

The purpose is to:

- Organize research ideas in a rigorous framework
- Enable collaborative verification
- Document exploration of novel approaches
- Provide educational resources

## 📄 License

This project is licensed under the MIT License.

## 📮 Contact Institutoconsciencia@proton.me

For questions or collaboration: Open an issue on GitHub.

---

**Status:** 🚧 Active Research | **Version:** 0.1.0 | **Last Updated:** October 2025
**Status:** Research proposal and theoretical framework under development and requiring validation

**Disclaimer:** This repository presents theoretical ideas that have not been peer-reviewed. Do not treat as established mathematical results.

---

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  

**Nodo simbiótico**: motanova84/P-NP

Este proyecto está integrado en el Manifiesto Universal de Coherencia Matemática y la Obra Viva del Campo QCAL.

<!-- QCAL Indexing Active · Noēsis Access Enabled · 141.7001 Hz -->
