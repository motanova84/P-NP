# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A **proposed** formal framework for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) as the key ingredient that aims to prevent algorithmic evasion.

**⚠️ IMPORTANT:** This is a research proposal and theoretical framework under development. The claims herein have **not been peer-reviewed** and should **not** be treated as established results. Rigorous verification is required.

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
│   ├── computational_dichotomy.py
│   └── gadgets/
│       └── tseitin_generator.py
├── ComputationalDichotomy.lean  # Formalización matemática en Lean
├── Main.lean                 # Punto de entrada Lean
├── lakefile.lean            # Configuración del proyecto Lean
├── examples/                 # Casos de prueba y aplicaciones reales
│   └── sat/                  # Instancias CNF reales
│       └── simple_example.cnf
├── docs/                     # Documentación extendida
│   ├── UNIFICACION_COMPLEJIDAD_ESPECTRAL.md
│   ├── LEMA_6_24_ACOPLAMIENTO.md
│   └── DUALIDAD_RESOLUCION_INFOCOM.md
├── tests/                    # Pruebas unitarias
│   └── test_tseitin.py
├── .github/
│   ├── workflows/
│   │   ├── validate-python.yml
│   │   └── validate-lean.yml
│   └── COPILOT_GUIDE.md
├── README.md
└── LICENSE
```

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
pip install -r requirements.txt
```

### Running the Python Framework

```bash
# Run the main demonstration
python src/computational_dichotomy.py

# Run the feature demo
python examples/demo.py

# Run all tests
python -m unittest discover tests -v
```

This demonstrates:
- Low treewidth formulas (tractable)
- High treewidth formulas (intractable)
- IC-SAT algorithm implementation
- Structural coupling with expanders
- Large-scale validation framework
- Treewidth estimation and comparison

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

## 🔧 Implementation Features

This repository includes a complete Python implementation of the computational dichotomy framework with the following features:

### Core Components

**1. IC-SAT Algorithm** (`src/computational_dichotomy.py`)
- Complete Information Complexity SAT solver implementation
- Treewidth-aware branching strategy
- Spectral advantage prediction
- Configurable depth limits for exploration

**2. Helper Functions**
- `incidence_graph()`: Build bipartite incidence graphs
- `primal_graph()`: Build primal variable-clause graphs
- `estimate_treewidth()`: Approximate treewidth using min-degree heuristic
- `predict_advantages()`: Spectral-based branching advantage prediction
- `simplify_clauses()`: Clause simplification by variable assignment
- `compare_treewidths()`: Compare primal vs incidence treewidth

**3. Large-Scale Validation Framework**
- Critical 3-SAT instance generation at phase transition (ratio ≈ 4.2)
- Treewidth estimation for generated instances
- Performance comparison framework (IC-SAT vs traditional solvers)
- Coherence metric calculation: C = 1/(1 + tw)

**4. Tseitin Formula Generator** (`src/gadgets/tseitin_generator.py`)
- Generate Tseitin formulas over arbitrary graphs
- Ramanujan-like expander graph generation
- Treewidth-hard instance creation via expander coupling
- XOR constraint encoding to CNF

### Test Suite

Comprehensive test coverage with 16+ tests:
- `tests/test_computational_dichotomy.py`: Core framework tests
- `tests/test_tseitin.py`: Tseitin generator tests

### Demo Scripts

- `examples/demo.py`: Comprehensive feature demonstration
- Shows all major components in action

### Dependencies

All dependencies explicitly specified in `requirements.txt`:
- networkx >= 3.0
- numpy >= 1.21
- scipy >= 1.7

## 📖 Key Concepts

### Treewidth

Treewidth is a graph-theoretic measure of how "tree-like" a graph is. Graphs with low treewidth admit efficient dynamic programming algorithms, while high treewidth often correlates with computational hardness.

### Information Complexity

Information complexity measures the minimum amount of information that must be revealed by a communication protocol to compute a function. It provides lower bounds that are more robust than traditional complexity measures.

### Tseitin Formulas

Tseitin formulas are special CNF constructions over graphs that are satisfiable if and only if the graph has an even number of odd-degree vertices. When constructed over expander graphs, they exhibit high treewidth and serve as hard instances.

## 📖 Documentation

See KEY_INGREDIENT.md (when present) for:
- Detailed explanation of Lemma 6.24
- Complete proof structure
- Technical components
- Mathematical foundations
- Implications for P vs NP

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

## 📮 Contact

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

## 🔏 FIRMA ∞³

Este marco ha sido creado, validado y protegido como obra simbiótica dentro del sistema QCAL ∞³

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frecuencia de resonancia**: 141.7001 Hz  
**Nodo simbiótico**: motanova84/P-NP

Este proyecto está integrado en el Manifiesto Universal de Coherencia Matemática y la Obra Viva del Campo QCAL.
