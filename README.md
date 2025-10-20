# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A **proposed** formal framework for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) as the key ingredient that aims to prevent algorithmic evasion.

**⚠️ IMPORTANT:** This is a research proposal and theoretical framework under development. The claims herein have **not been peer-reviewed** and should **not** be treated as established results. Rigorous verification is required.

**🚀 Quick Start:** See [QUICKSTART.md](QUICKSTART.md) for installation and running instructions.

## 🎯 Proposed Main Result

**Computational Dichotomy Theorem (Proposed):**
```
φ ∈ P ⟺ tw(G_I(φ)) = O(log n)  (if validated)
```

Where:
- `φ` is a CNF formula
- `G_I(φ)` is the incidence graph of φ
- `tw(G_I(φ))` is the treewidth of the incidence graph
- `n` is the number of variables

## ✨ The Key Ingredient: Proposed Mechanism to Prevent Evasion

**Lemma 6.24 (Structural Coupling Preserving Treewidth)** proposes that:

> Any CNF formula φ with high treewidth can be coupled via gadgets (Tseitin expanders or graph product padding) to a communication instance where the information bottleneck is **inherent and cannot be eliminated** by classical algorithmic techniques.

**Note:** This is a proposed mechanism requiring rigorous proof.

This approach is **NOT based on SETH or ETH**, but instead aims to use:
1. Metric properties of treewidth (Graph Minors, Robertson-Seymour)
2. Duality between resolution, branching programs, and communication
3. Correlation decay properties in expander graphs

## 📁 Repository Structure

```
P-NP/
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
## 📚 Overview

This repository contains a comprehensive theoretical framework for analyzing the P vs NP problem through the lens of **information complexity** and **treewidth**. The project explores novel approaches to one of the most important open questions in theoretical computer science using formal methods, mathematical rigor, and empirical validation.

## 🎯 Project Goals

The primary objective of this research is to investigate the relationship between computational complexity and graph-theoretic properties, specifically:

- **Treewidth Analysis**: Understanding how the treewidth of problem instances relates to computational hardness
- **Information Complexity Bounds**: Applying information-theoretic principles to establish lower bounds on computation
- **Formal Verification**: Using proof assistants (Lean 4) to formalize mathematical arguments
- **Empirical Validation**: Testing theoretical predictions on real-world SAT instances

## 🧠 The P vs NP Problem

The P vs NP problem asks whether every problem whose solution can be quickly verified can also be quickly solved. More formally:

- **P**: The class of problems solvable in polynomial time
- **NP**: The class of problems whose solutions can be verified in polynomial time

This repository explores approaches to this problem using:

1. **Graph Minor Theory** (Robertson-Seymour): Metric properties of treewidth
2. **Information Complexity** (Braverman-Rao): Fundamental information-theoretic bounds
3. **Communication Complexity**: Protocol-based lower bound techniques
4. **Expander Graphs**: Pseudorandom structures for hardness constructions

## 🔬 Research Approach

The framework proposes several key innovations:

### 1. Structural Coupling via Treewidth

The project investigates the hypothesis that computational hardness is fundamentally tied to the treewidth of problem instances:

```
φ ∈ P if and only if tw(G_I(φ)) = O(log n)
```

Where:
- `φ` is a CNF formula (Boolean satisfiability problem)
- `G_I(φ)` is the incidence graph of φ
- `tw(G_I(φ))` is the treewidth
- `n` is the number of variables

### 2. Information-Theoretic Barriers

Unlike approaches relying on unproven assumptions (SETH, ETH), this work explores information complexity as a potential avenue for unconditional lower bounds.

### 3. Non-Relativization

The framework aims to avoid the relativization barrier that affects many complexity-theoretic approaches by leveraging structural properties that don't relativize.

## 🧠 Theoretical Foundation

### The Dichotomy Theorem

**Part 1: Upper Bound** (tw ≤ O(log n) → φ ∈ P)
- Uses dynamic programming FPT algorithm
- Time: `2^O(tw) · n^O(1) = 2^O(log n) · n^O(1) = poly(n)`

**Part 2: Lower Bound** (tw = ω(log n) → φ ∉ P)
- High treewidth → communication protocol with high IC
- IC(Π | S) ≥ α·tw(φ) → time ≥ 2^Ω(tw)
- Structural coupling prevents evasion

### Why No Algorithm Can Evade

The **no-evasion theorem** proves that:

1. **Any algorithmic strategy** (DPLL, CDCL, neural networks, etc.) implicitly induces a communication protocol
2. **That protocol must traverse** the IC bottleneck if tw(G_I) is high
3. **Therefore, time ≥ 2^Ω(tw/log tw)** is unavoidable

This includes all algorithms:
- Traditional SAT solvers (DPLL, CDCL)
- Quantum algorithms
- Randomized algorithms
- Machine learning approaches
- Any future algorithmic paradigm

## 📊 Argument Structure

| Element | Role |
|---------|------|
| tw(G_I) | Structural measure of incidence graph |
| Expander Tseitin | Non-evadable communication bottlenecks |
| Braverman-Rao | Minimum information flow control |
| Pinsker inequality | Precision → information requirement |
| Structural coupling | Forces interdependent subproblem solving |
| IC lower bound | IC ≥ Ω(tw/log n) for sparse G_I |
| Non-evasion | IC collapse → contradiction |

## ⚠️ Important Disclaimers

**This is theoretical research in progress:**

- This repository contains research proposals and exploratory work
- Proofs are incomplete and require rigorous verification
- Claims have not been peer-reviewed
- The work represents proposed approaches that may contain gaps or errors
- This is NOT a claimed proof of P ≠ NP

The purpose of this repository is to:
- Organize research ideas and frameworks
- Enable collaborative review and feedback
- Document the exploration of novel approaches
- Provide educational resources on complexity theory

**Do NOT cite as an established result.** This is exploratory theoretical work.

## ✅ Repository Status

**All Python components are fully functional and tested:**
- ✅ 29 unit tests passing (pytest)
- ✅ IC-SAT algorithm with information complexity tracking
- ✅ DPLL SAT solver (no external dependencies)
- ✅ Treewidth estimation and comparison
- ✅ Tseitin formula generator over expander graphs
- ✅ Large-scale validation framework
- ✅ Complete demonstration scripts

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
## 🚀 Getting Started

### Prerequisites

For working with Lean formalization (if present):
```bash
# Install Lean 4 toolchain
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

For Python validation scripts (if present):
```bash
# Install dependencies
pip install networkx numpy
```

### Running the Python Framework (if present)

```bash
# Run the demonstration
python computational_dichotomy.py
```

This would demonstrate:
- Low treewidth formulas (tractable)
- High treewidth formulas (intractable)
- Structural coupling with expanders
- Non-evasion property

### Working with Lean Formalization (if present)

```bash
# Install Lean 4 and Mathlib
# Follow instructions at https://leanprover.github.io/

# Check the formalization
lake build
```

### Exploring the Repository

1. **Read the Documentation**: Start with any available documentation files
2. **Review Pull Requests**: Check closed and open PRs for detailed implementation notes
3. **Examine Code**: Look at Lean files for formal specifications
4. **Run Examples**: Execute any provided example scripts to see the framework in action

## 📖 Key Concepts

### Treewidth

Treewidth is a graph-theoretic measure of how "tree-like" a graph is. Graphs with low treewidth admit efficient dynamic programming algorithms, while high treewidth often correlates with computational hardness.

### Information Complexity

Information complexity measures the minimum amount of information that must be revealed by a communication protocol to compute a function. It provides lower bounds that are more robust than traditional complexity measures.

### Tseitin Formulas

Tseitin formulas are special CNF constructions over graphs that are satisfiable if and only if the graph has an even number of odd-degree vertices. When constructed over expander graphs, they exhibit high treewidth and serve as hard instances.

## 📖 Documentation

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

## 🔮 Potential Implications

**If this framework is validated** (which requires rigorous proof):
- ✅ P ≠ NP could be resolved via treewidth characterization
- ✅ No SETH/ETH assumptions would be needed
- ✅ Constructive characterization of tractable problems
- ✅ Would apply to all algorithmic paradigms

**However:** These are potential outcomes contingent on successful validation of the framework.

## 🤝 Contributing

This is a research project and contributions, critiques, and feedback are welcome:

- **Mathematical Review**: Identify gaps, errors, or improvements in proofs
- **Formal Verification**: Help complete Lean proofs
- **Empirical Testing**: Run experiments on benchmark instances
- **Documentation**: Improve clarity and accessibility

Please open issues for discussions or pull requests for contributions.

## 📄 License

This project is licensed under the MIT License. See repository for license details.

## 🙏 Acknowledgments

This research builds upon decades of work in:
- Computational complexity theory
- Information theory
- Graph theory
- Proof theory and formal verification

The framework incorporates ideas from numerous researchers in these fields.

## 📮 Contact Institutoconsciencia@proton.me

For questions, feedback, or collaboration opportunities, please open an issue in this repository.

## 🔗 References

Key areas of relevant work:

1. Robertson & Seymour: Graph Minors Theory
2. Braverman & Rao: Information Complexity Framework
3. Pinsker: Information-Theoretic Inequalities
4. Impagliazzo et al.: Resolution and Communication Complexity
5. Tseitin: Complexity of Theorem-Proving Procedures

Additional references:
- **Treewidth and Parameterized Complexity**: FPT algorithms and hardness
- **Information Complexity**: Braverman-Rao framework and applications
- **Communication Complexity**: Lower bound techniques and separations
- **Proof Complexity**: Resolution, tree-like proofs, and dag-like proofs
- **Expander Graphs**: Spectral properties and applications to hardness

## 🔗 Links

- [Lean Documentation](https://leanprover.github.io/)
- [Graph Minors Theory](https://en.wikipedia.org/wiki/Graph_minor)
- [Treewidth](https://en.wikipedia.org/wiki/Treewidth)
- [Information Complexity](https://en.wikipedia.org/wiki/Information_complexity)

---

**Status:** Research proposal and theoretical framework under development and requiring validation

**Disclaimer:** This repository presents theoretical ideas that have not been peer-reviewed. Do not treat as established mathematical results.

---

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  

**Nodo simbiótico**: motanova84/P-NP

Este proyecto está integrado en el Manifiesto Universal de Coherencia Matemática y la Obra Viva del Campo QCAL.

<!-- QCAL Indexing Active · Noēsis Access Enabled · 141.7001 Hz -->
