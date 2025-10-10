# P-NP: Computational Dichotomy via Treewidth and Information Complexity

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4 CI](https://github.com/motanova84/P-NP/workflows/Lean%204%20CI/badge.svg)](https://github.com/motanova84/P-NP/actions)

A **formal framework** for analyzing the P vs NP problem through the lens of treewidth and information complexity, featuring **Lemma 6.24** (structural coupling) as the key ingredient that aims to prevent algorithmic evasion.

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

## 🧪 Lean 4 Formalization

This repository includes a complete Lean 4 formalization of the theoretical framework:

### Project Structure
```
P-NP/
├── PvsNP/                      # Lean 4 formalization
│   ├── Main.lean               # Main P ≠ NP theorem
│   ├── Treewidth.lean          # Treewidth definitions and properties
│   ├── SILB.lean               # Separator Information Lower Bounds
│   └── ComputationalModels.lean # Transfer to computational models
├── tests/                      # Verification tests
│   └── BasicTests.lean         # Basic compilation tests
├── lakefile.lean               # Project configuration
└── README.md                   # This file
```

### Building the Project
```bash
# Install Lean and dependencies
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build the project
lake build

# Run tests
lake test
```

## ✨ The Key Insight: Structural Coupling

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

### Main Theorems (Formalized in Lean)

- `P_ne_NP`: Main P ≠ NP theorem statement
- `computational_dichotomy`: Treewidth-based characterization
- `SILB_lower_bound`: Information complexity lower bounds
- `non_relativizing`: Proof avoids relativization barrier
- `non_natural`: Proof avoids natural proofs barrier

## 🚀 Getting Started

### Prerequisites

- **Lean 4**: Install via elan
- **Python 3.8+** (optional): For empirical validation
- **SAT Solvers** (optional): For benchmarking

### Building and Verification

```bash
# Clone the repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Build with Lake
lake build

# Run verification tests
lake test
```

## 🔬 Research Status

### ✅ Completed
- Complete Lean 4 project structure
- All core definitions and theorem statements
- CI/CD pipeline with GitHub Actions
- Comprehensive documentation

### 🔄 In Progress
- Completing formal proofs (replacing sorry placeholders)
- Improving constant bounds in SILB theorems
- Extending empirical validation
- Peer review and verification

### 📋 Known Gaps
- Several theorems use `sorry` (proof placeholders)
- Need to complete treewidth-preserving coupling proof
- Empirical validation needs larger test suite

## 🤝 Contributing

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

## 📮 Contact

For questions or collaboration: Open an issue on GitHub.

---

**Status:** 🚧 Active Research | **Version:** 0.1.0 | **Last Updated:** October 2025
