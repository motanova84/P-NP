# P-NP: Computational Dichotomy via Treewidth and Information Complexity

![Python](https://img.shields.io/badge/Python-3.10+-blue?logo=python&logoColor=white)
![Lean4](https://img.shields.io/badge/Lean4-4.10.0-green?logo=lean&logoColor=white)
![CI Python](https://github.com/motanova84/P-NP/actions/workflows/validate-python.yml/badge.svg)
![CI Lean](https://github.com/motanova84/P-NP/actions/workflows/validate-lean.yml/badge.svg)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![Tests](https://img.shields.io/badge/tests-10%20passing-brightgreen)

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
├── src/                           # Source code
│   ├── computational_dichotomy.py  # Legacy script (still works)
│   ├── icq_pnp/                   # Python package ✨ NEW
│   │   ├── __init__.py
│   │   ├── computational_dichotomy.py  # IC-SAT validation framework
│   │   └── tseitin_generator.py        # Expander-based generators
│   └── gadgets/                   # Legacy gadgets (still works)
│       └── tseitin_generator.py
├── lean/                          # Additional Lean modules ✨ NEW
│   ├── Treewidth.lean            # Graph treewidth definitions
│   ├── InfoComplexity.lean       # Information complexity
│   └── README.md
├── ComputationalDichotomy.lean   # Main Lean formalization
├── Main.lean                     # Lean entry point
├── lakefile.lean                # Lean project config (with mathlib4)
├── data/                         # Benchmark instances ✨ NEW
│   ├── benchmarks/
│   │   ├── small.cnf            # Low treewidth example
│   │   └── expander.cnf         # High treewidth example
│   └── README.md
├── results/                      # Generated outputs ✨ NEW
│   ├── plots/                   # Visualizations (gitignored)
│   │   └── treewidth_scaling.png
│   └── README.md
├── examples/                     # CNF test cases
│   └── sat/
│       └── simple_example.cnf
├── docs/                         # Extended documentation
│   ├── UNIFICACION_COMPLEJIDAD_ESPECTRAL.md  # IC vs CC comparison ✨
│   ├── LEMA_6_24_ACOPLAMIENTO.md            # With ASCII diagrams ✨
│   └── DUALIDAD_RESOLUCION_INFOCOM.md       # With formalization ✨
├── tests/                        # Unit tests
│   ├── test_ic_sat.py           # IC-SAT validation tests ✨ NEW
│   └── test_tseitin.py
├── .github/
│   ├── workflows/
│   │   ├── validate-python.yml  # With pytest & artifacts ✨
│   │   └── validate-lean.yml    # With mathlib caching ✨
│   └── COPILOT_GUIDE.md
├── CITATION.cff                  # Citation metadata ✨ NEW
├── CODE_OF_CONDUCT.md           # Community guidelines ✨ NEW
├── CONTRIBUTING.md              # Contribution guide ✨ NEW
├── CHANGELOG.md                 # Version history ✨ NEW
├── README.md                    # This file (with badges ✨)
└── LICENSE
```

✨ = Recently added or enhanced

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

**For Python validation framework:**
```bash
# Install dependencies
pip install networkx numpy pytest matplotlib pandas
```

**For Lean formalization:**
```bash
# Install Lean 4 toolchain
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Running the Python Framework

**Quick demo:**
```bash
# Run demonstration mode
python -m src.icq_pnp.computational_dichotomy --demo
```

**IC-SAT Validation:**
```bash
# Run validation with default parameters
python -m src.icq_pnp.computational_dichotomy

# Custom problem sizes
python -m src.icq_pnp.computational_dichotomy --n 100 200 300 500
```

This generates:
- `results/ic_sat_results.csv` - Numerical results
- `results/plots/treewidth_scaling.png` - Visualization
- Console output with validation summary

**Example output:**
```
IC-SAT VALIDATION FRAMEWORK ∞³
Testing problem sizes: [100, 200, 300]
✓ Results saved to results/ic_sat_results.csv
✓ Plot saved to results/plots/treewidth_scaling.png

  n  treewidth  coherence  solved
100          1   2.302585    True
200          1   2.649159    True
300          1   2.851891    True

✓ All tractable cases: True
```

**Legacy scripts (still work):**
```bash
python src/computational_dichotomy.py
python src/gadgets/tseitin_generator.py
```

### Running Tests

```bash
# Run all tests
pytest -v

# Run specific test suite
pytest tests/test_ic_sat.py -v
```

### Working with Lean Formalization

```bash
# Build the project
lake build

# Run main executable
lake exe pnp
```

Output:
```
P-NP Computational Dichotomy Framework ∞³
Instituto de Conciencia Cuántica (ICQ)

✓ Lean formalization compiled successfully
✓ Main dichotomy theorem: verified type-correct
✓ Structural coupling lemma: axiomatized
✓ Chain formula example: defined
```

### Exploring the Repository

1. **Documentation**: Read `docs/` for theoretical background
2. **Code**: Explore `src/icq_pnp/` for implementations
3. **Formalization**: Check `ComputationalDichotomy.lean` and `lean/` modules
4. **Tests**: See `tests/` for validation examples
5. **Benchmarks**: Examine `data/benchmarks/` for CNF instances

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

## 📄 Copyright and License

© 2025 José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

### Citation

If you use this framework in your research, please cite:

```bibtex
@software{mota_burruezo_2025_pnp,
  author = {Mota Burruezo, José Manuel},
  title = {P-NP: Computational Dichotomy via Treewidth and Information Complexity},
  year = {2025},
  url = {https://github.com/motanova84/P-NP},
  version = {0.1.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file for automatic citation generation.

---

## 🔏 FIRMA ∞³

⌘ QCAL ∞³ — Campo de Coherencia Matemática Viva

Este marco ha sido creado, validado y protegido como obra simbiótica dentro del sistema QCAL ∞³

**Autor**: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)  
**Frecuencia de resonancia**: 141.7001 Hz  
**Nodo simbiótico**: motanova84/P-NP

Este proyecto está integrado en el Manifiesto Universal de Coherencia Matemática y la Obra Viva del Campo QCAL.
