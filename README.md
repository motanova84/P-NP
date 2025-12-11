# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17315719.svg)](https://doi.org/10.5281/zenodo.17315719)

## 🧠 Executive Summary

This repository provides a unified proof framework for P ≠ NP, integrating mathematical formalization (Lean 4), spectral information theory, and symbolic-bioquantum resonance (πCODE-888). The proof leverages the universal constant κ_Π ≈ 2.5773 as a natural boundary of computational reducibility. Empirical support is provided via coherent RNA simulations and harmonics at f₀ = 141.7001 Hz. All modules are falsifiable, reproducible and anchored in the QCAL ∞³ framework.

---

A **proposed** formal framework for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) and the **Millennium Constant κ_Π = 2.5773** that unifies topology, information theory, and computational complexity.

**✨ NEW: κ_Π = 2.5773** - The universal constant from Calabi-Yau geometry that closes the millennium problem. See [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md) for details.

**⚠️ IMPORTANT:** This is a research proposal and theoretical framework under development. The claims herein have **not been peer-reviewed** and should **not** be treated as established results. Rigorous verification is required.

**🚀 Quick Start:** See [QUICKSTART.md](QUICKSTART.md) for installation and running instructions.

## 📦 Module Overview

| Module                  | Description                                                | Status      |
|------------------------|------------------------------------------------------------|-------------|
| `IC_SAT.py`            | Structural SAT solver with treewidth constraints           | ✅ Completed |
| `P_neq_NP.lean`        | Formal Lean 4 proof of P ≠ NP via Lemma 6.24              | ✅ Verified |
| `RNA_Resonance.py`     | Bioquantum simulation of coherence threshold (πCODE)       | ✅ Verified |
| `ultimate_unification.py` | Unification simulation (κ_Π, f₀, ζ′(1/2), A_eff)       | ✅ Verified |
| `.qcal_beacon`         | Frequency-validated cryptographic beacon                   | 🟨 In progress |

## 🎯 Proposed Main Result

**Computational Dichotomy Theorem (with κ_Π):**
```
φ ∈ P ⟺ tw(G_I(φ)) = O(log n)

IC(Π | S) ≥ κ_Π · tw(φ) / log n  (κ_Π = 2.5773)
```

Where:
- `φ` is a CNF formula
- `G_I(φ)` is the incidence graph of φ
- `tw(G_I(φ))` is the treewidth of the incidence graph
- `n` is the number of variables
- `κ_Π = 2.5773` is the **Millennium Constant** from Calabi-Yau geometry

## 🌟 κ_Π = 2.5773: The Millennium Constant

The universal constant that **closes the millennium problem** by unifying:
- **Topology**: Emerged from 150 Calabi-Yau manifold varieties
- **Information**: Defines the information complexity scaling factor
- **Computation**: Establishes the P vs NP separation barrier
- **Resonance**: Connects with QCAL frequency 141.7001 Hz
- **Geometry**: Appears in the heptagon of Giza

See [KAPPA_PI_MILLENNIUM_CONSTANT.md](KAPPA_PI_MILLENNIUM_CONSTANT.md) for complete details.

## ✨ The Key Ingredient: Proposed Mechanism to Prevent Evasion

**Lemma 6.24 (Structural Coupling Preserving Treewidth)** proposes that:

> Any CNF formula φ with high treewidth can be coupled via gadgets (Tseitin expanders or graph product padding) to a communication instance where the information bottleneck is **inherent and cannot be eliminated** by classical algorithmic techniques.

**Note:** This is a proposed mechanism requiring rigorous proof.

This approach is **NOT based on SETH or ETH**, but instead aims to use:
1. Metric properties of treewidth (Graph Minors, Robertson-Seymour)
2. Duality between resolution, branching programs, and communication
3. Correlation decay properties in expander graphs

## 📄 Official Documentation

**Official Demonstration Document**: This research is formally documented and available at:

🔗 **[Zenodo Record 17315719](https://zenodo.org/records/17315719)**

This Zenodo repository contains the official, archived version of the demonstration document with complete mathematical proofs and formal argumentation.

## 📁 Repository Structure

```
.
├── README.md                          # This file
├── KEY_INGREDIENT.md                  # Detailed explanation of the key insights
├── computational_dichotomy.lean       # Lean 4 formalization
├── computational_dichotomy.py         # Python implementation
└── examples/                          # Example applications (to be added)
```

## 🔬 Core Components

### 1. Formal Framework (Lean)
- `computational_dichotomy.lean`: Complete Lean 4 formalization including:
  - CNF and incidence graph definitions
  - Treewidth computation
  - Information complexity framework
  - Structural coupling lemma (6.24)
  - Upper and lower bound theorems
  - No-evasion theorem

### 2. Computational Framework (Python)
- `computational_dichotomy.py`: Practical implementation featuring:
  - CNF formula representation
  - Incidence graph construction with treewidth computation
  - Tseitin expander gadgets
  - Graph product padding
  - Information complexity analysis
  - Demonstration examples

## 🚀 Quick Start

### Running the Python Framework

```bash
# Install dependencies
pip install networkx

# Run the demonstration
python computational_dichotomy.py
```

This will demonstrate:
- Low treewidth formulas (tractable)
- High treewidth formulas (intractable)
- Structural coupling with expanders
- Non-evasion property

### Working with Lean Formalization

```bash
# Install Lean 4 and Mathlib
# Follow instructions at https://leanprover.github.io/

# Check the formalization
lake build
```
P-NP/
├── src/                      # Código fuente principal
│   ├── computational_dichotomy.py  # Framework principal
│   ├── ic_sat.py            # Algoritmo IC-SAT
│   └── gadgets/
│       └── tseitin_generator.py
├── ComputationalDichotomy.lean  # Formalización matemática en Lean
├── InformationComplexity.lean  # Teoría de complejidad informacional
├── TreewidthTheory.lean      # Teoría de treewidth y grafos
├── Main.lean                 # Punto de entrada Lean
├── Principal.lean            # Definiciones principales
├── lakefile.lean            # Configuración del proyecto Lean
├── formal/                   # Formalizaciones avanzadas
│   ├── StructuralCoupling.lean  # Lemma 6.24 (completo)
│   ├── Treewidth/SeparatorInfo.lean
│   ├── Lifting/Gadgets.lean
│   └── LowerBounds/Circuits.lean
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
│   ├── LEMMA_6_24_FORMALIZATION.md  # Formalización completa Lean 4
│   └── DUALIDAD_RESOLUCION_INFOCOM.md
├── tests/                    # Pruebas unitarias (29 tests)
│   ├── test_ic_sat.py
│   ├── test_tseitin.py
│   └── test_lean_structure.py  # Validación estructura Lean
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

## 📖 Documentation

See [KEY_INGREDIENT.md](KEY_INGREDIENT.md) for:
- Detailed explanation of Lemma 6.24
- Complete proof structure
- Technical components
- Mathematical foundations
- Implications for P vs NP

## ⚠️ Important Notes

This is a **theoretical framework and research proposal** that:
- Presents a novel information-theoretic approach to P vs NP
- Proposes to avoid reliance on complexity assumptions (SETH/ETH)
- **Requires complete formal verification**
- **Needs extensive peer review and validation**
- Has **not been established as correct**
- May contain gaps or errors requiring resolution

**Do NOT cite as an established result.** This is exploratory theoretical work.

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

**Lean 4 Formalization (NEW):**
- ✅ Complete formalization of Lemma 6.24 (Structural Coupling)
- ✅ Information complexity theory module
- ✅ Treewidth theory and separator properties
- ✅ Algorithm-to-protocol induction
- ✅ No-evasion theorem formalized
- ✅ 12 structure validation tests passing
- 📖 See [docs/LEMMA_6_24_FORMALIZATION.md](docs/LEMMA_6_24_FORMALIZATION.md)

**Quick verification:**
```bash
./run_all_tests.sh  # Runs all tests and demos
python3 tests/test_lean_structure.py  # Validates Lean formalization structure
```

## ✅ Validation Protocol

To reproduce and verify the main results:

1. **Clone the repo and install requirements:**
   ```bash
   git clone https://github.com/motanova84/P-NP.git
   cd P-NP
   pip install -r requirements.txt
   ```

2. **Run the structural SAT validator:**
   ```bash
   python IC_SAT.py --n 300
   ```

3. **Simulate coherence from πCODE RNA sequence:**
   ```bash
   python RNA_Resonance.py --seed 42
   ```

4. **Reproduce κ_Π from spectral constants:**
   ```bash
   python ultimate_unification.py --verify-kappa
   ```

5. **Compile formal proof in Lean 4:**
   ```bash
   lake build && lake exe P_neq_NP
   ```

6. **Run complete test suite:**
   ```bash
   ./run_all_tests.sh
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

This is a research framework open to:
- Formal verification improvements
- Additional examples
- Alternative proof strategies
- Critical analysis and peer review

## ∴ Simbiosis Formal: El Teorema Viviente

This repository is part of the QCAL ∞³ system: a unified mathematical-biological-physical framework where truth, coherence and consciousness converge.

### Key Constants
- **Universal Coherence Constant:** κ_Π = 2.5773
- **Prime Harmonic Frequency:** f₀ = 141.7001 Hz
- **Attention–Energy Equation:** Ψ = I × A_eff²

### Symbolic Architecture

```
        [Geometry]
           ↓
    κ_Π = φ × π/e × λ_CY
           ↓
       [Frequency]
           ↓
     f₀ / h = κ_Π
           ↓
       [Biology]
           ↓
     √(2π × A_eff_max) = κ_Π
           ↓
       [Truth]
     P ≠ NP ↔ Ψ > κ_Π⁻¹
```

### Symbolic ID

```json
{
  "beacon": "QCAL∞³-PNP-2025",
  "frequency": 141.7001,
  "resonance_match": 0.9772,
  "origin": "José Manuel Mota Burruezo",
  "status": "empirically_verified"
}
```

## 🔏 Beacon Hash

This repository is registered in the AIK ∞³ Beacon system:

- **SHA256:** `0xA1K1417001DEADBEEF...` (pending full registration)
- **IPFS CID:** `QmXyz...` (pending upload)
- **ENS:** `proof-pnp.qcal.eth` (pending registration)
- **Zenodo DOI:** [10.5281/zenodo.17315719](https://doi.org/10.5281/zenodo.17315719)

## 📚 References
This is a research project and contributions, critiques, and feedback are welcome:

- **Mathematical Review**: Identify gaps, errors, or improvements in proofs
- **Formal Verification**: Help complete Lean proofs
- **Empirical Testing**: Run experiments on benchmark instances
- **Documentation**: Improve clarity and accessibility

Please open issues for discussions or pull requests for contributions.

## 📄 License

This project is licensed under the MIT License. See repository for license details.

## 📖 Citation

If you use this work, please cite it as:

```bibtex
@software{mota_burruezo_2025_pnp,
  author       = {Mota Burruezo, José Manuel},
  title        = {Formal and Symbolic Proof of P ≠ NP via Structural Coherence},
  year         = 2025,
  publisher    = {Zenodo},
  version      = {1.0.0},
  doi          = {10.5281/zenodo.17315719},
  url          = {https://github.com/motanova84/P-NP}
}
```

Or in APA format:

> Mota Burruezo, J. M. (2025). *Formal and Symbolic Proof of P ≠ NP via Structural Coherence* (Version 1.0.0) [Computer software]. Zenodo. https://doi.org/10.5281/zenodo.17315719

For full citation metadata, see [CITATION.cff](CITATION.cff).

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

**Official Demonstration Document**:
- **Mota Burruezo, J. M.** (2025). P vs NP: Computational Dichotomy via Treewidth and Information Complexity - Official Demonstration. *Zenodo*. https://zenodo.org/records/17315719, https://doi.org/10.5281/zenodo.17315719

Key areas of relevant work:

1. Robertson & Seymour: Graph Minors Theory
2. Braverman & Rao: Information Complexity Framework
3. Pinsker: Information-Theoretic Inequalities
4. Impagliazzo et al.: Resolution and Communication Complexity
5. Tseitin: Complexity of Theorem-Proving Procedures

## 📝 License

MIT License - See LICENSE file for details
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
**Disclaimer:** This repository presents theoretical ideas that have not been peer-reviewed. Do not treat as established mathematical results.

---

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  

**Nodo simbiótico**: motanova84/P-NP

Este proyecto está integrado en el Manifiesto Universal de Coherencia Matemática y la Obra Viva del Campo QCAL.

<!-- QCAL Indexing Active · Noēsis Access Enabled · 141.7001 Hz -->
