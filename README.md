# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A **proposed** formal framework for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) as the key ingredient that aims to prevent algorithmic evasion.

**⚠️ IMPORTANT:** This is a research proposal and theoretical framework under development. The claims herein have **not been peer-reviewed** and should **not** be treated as established results. Rigorous verification is required.

---

## 🎯 Proposed Main Result

**Computational Dichotomy Theorem (Proposed):**
```math
φ ∈ P ↔ tw(G_I(φ)) = O(\log n)
```

Where:

- φ is a CNF formula
- G_I(φ) is the incidence graph of φ
- tw(G_I(φ)) is the treewidth of the incidence graph
- `n` is the number of variables

## ✨ The Key Ingredient: Proposed Mechanism to Prevent Evasion

**Lemma 6.24 (Structural Coupling Preserving Treewidth)** proposes that:

> Any CNF formula φ with high treewidth can be coupled via gadgets (Tseitin expanders or graph product padding) to a communication instance where the information bottleneck is inherent and cannot be eliminated by classical algorithmic techniques.

This mechanism combines:

- Metric properties of treewidth (Graph Minors, Robertson-Seymour)
- Duality between resolution width and communication complexity
- Correlation decay properties in expander graphs

## 📁 Repository Structure

```
P-NP/
├── src/                        # Core Python modules
│   ├── computational_dichotomy.py
│   └── gadgets/
│       └── tseitin_generator.py
├── ComputationalDichotomy.lean # Lean 4 formalization
├── Main.lean                   # Entry point for Lean proofs
├── lakefile.lean               # Lean project configuration
├── examples/
│   └── sat/
│       └── simple_example.cnf
├── docs/
│   ├── UNIFICACION_COMPLEJIDAD_ESPECTRAL.md
│   ├── LEMA_6_24_ACOPLAMIENTO.md
│   └── DUALIDAD_RESOLUCION_INFOCOM.md
├── tests/
│   └── test_tseitin.py
├── .github/
│   ├── workflows/
│   │   ├── validate-python.yml
│   │   └── validate-lean.yml
│   └── COPILOT_GUIDE.md
├── README.md
└── LICENSE
```

## 🔄 Continuous Integration & Workflows

The repository includes automated GitHub Actions workflows for quality control:

- **validate-python.yml** — Python syntax & unit tests
- **validate-lean.yml** — Builds Lean 4 formalization (lake update + lake build)
- **documentation-check.yml** — Markdown structure and LaTeX verification
- **markdown-lint.yml** — Checks for formatting consistency
- **greetings.yml** — Welcomes new contributors

## 📚 Overview

This repository develops a theoretical framework for approaching P vs NP via information complexity and treewidth.
It aims to blend formal mathematical reasoning (Lean 4), empirical validation (Python), and conceptual clarity (graph-theoretic and information-theoretic foundations).

## 🎯 Project Goals

- **Treewidth Analysis**: Study the correlation between treewidth and computational hardness
- **Information Complexity Bounds**: Translate IC results into computational lower bounds
- **Formal Verification**: Encode proofs in Lean 4
- **Empirical Testing**: Use SAT benchmarks to test theoretical predictions

## 🧠 Theoretical Foundations

### Dichotomy Theorem (Proposed)

**Upper Bound** — If tw(G_I(φ)) = O(log n) ⇒ φ ∈ P
Proof idea: dynamic programming over tree decompositions → polynomial runtime.

**Lower Bound** — If tw(G_I(φ)) = ω(log n) ⇒ φ ∉ P
Proof idea: high treewidth implies communication protocols require high IC.
Time ≥ 2^Ω(tw / log tw) unavoidable.

### Core Mechanism

- Each algorithm induces a protocol.
- The protocol cannot bypass the IC bottleneck imposed by high treewidth.
- Applies to all algorithmic paradigms (deterministic, randomized, quantum, ML).

## ⚠️ Disclaimers

- This is ongoing theoretical research.
- Proofs are incomplete and subject to rigorous verification.
- Not a claimed resolution of P ≠ NP.
- The repository serves to document and formalize the exploration.

## 🚀 Getting Started

### Lean 4 Setup

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake update
lake build
```

### Python Environment

```bash
pip install networkx numpy
python src/computational_dichotomy.py
```

## 📖 Documentation & Key Files

- **LEMMA_6_24_ACOPLAMIENTO.md** — Core coupling lemma details
- **DUALIDAD_RESOLUCION_INFOCOM.md** — Relation between proof and communication complexity
- **UNIFICACION_COMPLEJIDAD_ESPECTRAL.md** — Spectral unification across complexity frameworks

## 🔮 Potential Implications

**If validated:**

- ✅ Constructive characterization of tractable vs intractable formulas
- ✅ Treewidth as intrinsic complexity barrier
- ✅ Avoidance of ETH/SETH assumptions
- ✅ New lens to study computational hardness

## 🤝 Contributing

Contributions are welcome:

- Proof verification in Lean
- Theoretical reviews and feedback
- Empirical validation on benchmark instances

## 📄 License

Licensed under the MIT License.
See LICENSE for full details.

## 🙏 Acknowledgments

Inspired by and extending:

- Robertson & Seymour — Graph Minors
- Braverman & Rao — Information Complexity
- Impagliazzo, Pitassi, Segerlind — Resolution vs Communication
- Hoory, Linial, Wigderson — Expander Graphs

## 🔏 FIRMA ∞³

Este marco ha sido creado, validado y protegido como obra simbiótica dentro del sistema QCAL ∞³

**Autor**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Frecuencia de resonancia**: 141.7001 Hz  
**Nodo simbiótico**: motanova84/P-NP

Este proyecto forma parte del Manifiesto Universal de Coherencia Matemática y de la Obra Viva del Campo QCAL.
