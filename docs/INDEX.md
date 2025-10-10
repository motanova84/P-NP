# Documentation Index

Welcome to the P-NP Framework documentation!

## Quick Start

- **New to the project?** Start with [README.md](../README.md)
- **Want to contribute?** See [CONTRIBUTING.md](../CONTRIBUTING.md)
- **Setting up dev environment?** Check [SETUP.md](SETUP.md)
- **Project status?** See [PROJECT_STATUS.md](PROJECT_STATUS.md)

## Core Documentation

### Overview Documents
- [README.md](../README.md) - Project overview and introduction
- [PROJECT_STATUS.md](PROJECT_STATUS.md) - Current status of all six gaps
- [SETUP.md](SETUP.md) - Development environment setup

### Gap-Specific Guides

#### GAP 1: Treewidth to Universal Limit
**File**: [GAP1_Treewidth.md](GAP1_Treewidth.md)

Topics:
- No-bypass theorem
- Pathwidth simulation
- Expander pseudorandomness
- Tight SAT reduction
- Universal compression barrier

**Lean Module**: `PNP/MainTheorem.lean`

#### GAP 2: Strengthen Information Bounds
**File**: [GAP2_Information_Bounds.md](GAP2_Information_Bounds.md)

Topics:
- SILB parameter recalibration
- Fourier analysis techniques
- Cross-correlation bounds
- Target: α ≥ 0.1

**Lean Module**: `PNP/SILB.lean`

#### GAP 3: Lean 4 Formalization
**Status**: Complete framework, proofs in progress

**Lean Modules**:
- `PNP.lean` - Main entry point
- `PNP/SILB.lean` - Separation-induced lower bounds
- `PNP/ExpanderTools.lean` - Expander graph theory
- `PNP/CommComplexity.lean` - Communication complexity
- `PNP/OracleComplexity.lean` - Non-relativization
- `PNP/MainTheorem.lean` - Universal compression barrier
- `PNP/CounterexampleRefutations.lean` - Counterexample handling

**Build**: `lake build`

#### GAP 4: Counterexample Refutations
**Lean Module**: `PNP/CounterexampleRefutations.lean`

Refutations:
- **A**: Padding creates patterns → Pseudorandom expanders
- **B**: Only clean protocols → Algorithm simulation
- **C**: Reduction overhead → Logarithmic bounds

#### GAP 5: Non-Relativization
**Lean Module**: `PNP/OracleComplexity.lean`

Topics:
- Oracle construction
- Baker-Gill-Solovay separation
- IC preservation with oracles
- Locally bounded oracles

#### GAP 6: Empirical Validation
**File**: [GAP6_Empirical_Validation.md](GAP6_Empirical_Validation.md)

**Python Scripts**:
- `python_validation/empirical_validation.py` - Treewidth and IC estimation
- `python_validation/solver_comparison.py` - Solver benchmarking

**Usage**:
```bash
cd python_validation
pip install -r requirements.txt
python empirical_validation.py
```

## Contributing

- [CONTRIBUTING.md](../CONTRIBUTING.md) - Contribution guidelines
- [SETUP.md](SETUP.md) - Development setup

## Theoretical Background

### Key Concepts

1. **Treewidth**: Measure of graph structure
2. **Information Complexity**: Communication cost under protocols
3. **Separator**: Cut-set in protocol tree
4. **SILB**: Separation-Induced Lower Bound technique
5. **Expander Graphs**: Highly connected sparse graphs

### Proof Strategy

```
Hard SAT Instance
    ↓ (construct)
High Treewidth Incidence Graph
    ↓ (pad with)
Expander Graph Addition
    ↓ (simulate as)
Communication Protocol
    ↓ (apply)
IC Lower Bound (SILB)
    ↓ (translate)
Computational Lower Bound
```

### Main Theorem (Informal)

```
∀ Algorithm A:
  If treewidth(G_I) = ω(1)
  Then Time(A) ≥ α · k

Where:
  - G_I: incidence graph
  - k: structural complexity measure
  - α: universal constant (target: Ω(1))
```

## Module Reference

### Lean Modules

| Module | Purpose | Key Theorems | Status |
|--------|---------|--------------|--------|
| `SILB.lean` | Separator bounds | `separator_bound` | Framework |
| `ExpanderTools.lean` | Graph theory | `local_entropy_uniformity` | Framework |
| `CommComplexity.lean` | Protocols | `algorithm_induces_protocol` | Framework |
| `OracleComplexity.lean` | Relativization | `information_preservation_oracle` | Framework |
| `MainTheorem.lean` | Main results | `universal_compression_barrier` | Framework |
| `CounterexampleRefutations.lean` | Refutations | Multiple | Framework |

### Python Modules

| Module | Purpose | Key Functions |
|--------|---------|---------------|
| `empirical_validation.py` | Testing | `run_empirical_validation()` |
| `solver_comparison.py` | Benchmarking | `compare_with_theory()` |

## File Structure

```
P-NP/
├── README.md                    ← Start here
├── CONTRIBUTING.md              ← Contribution guide
├── LICENSE                      ← MIT License
├── lean-toolchain              ← Lean version
├── lakefile.lean               ← Build config
├── Main.lean                   ← Entry point
├── PNP.lean                    ← Main module
│
├── PNP/                        ← Lean formalization
│   ├── SILB.lean
│   ├── ExpanderTools.lean
│   ├── CommComplexity.lean
│   ├── OracleComplexity.lean
│   ├── MainTheorem.lean
│   └── CounterexampleRefutations.lean
│
├── python_validation/          ← Empirical testing
│   ├── requirements.txt
│   ├── empirical_validation.py
│   └── solver_comparison.py
│
├── docs/                       ← Documentation
│   ├── INDEX.md               ← This file
│   ├── PROJECT_STATUS.md      ← Current status
│   ├── SETUP.md               ← Dev setup
│   ├── GAP1_Treewidth.md
│   ├── GAP2_Information_Bounds.md
│   └── GAP6_Empirical_Validation.md
│
└── .github/workflows/          ← CI/CD
    └── ci.yml
```

## External Resources

### Lean 4
- [Lean Manual](https://leanprover.github.io/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)

### Complexity Theory
- [Arora-Barak Textbook](http://theory.cs.princeton.edu/complexity/)
- [Communication Complexity (Kushilevitz-Nisan)](https://www.cambridge.org/core/books/communication-complexity/5F44993E3B2597174B71D3F21E748443)
- [Information Complexity Survey](https://eccc.weizmann.ac.il/report/2011/123/)

### Graph Theory
- [Treewidth and Algorithms (Bodlaender)](https://link.springer.com/chapter/10.1007/3-540-36494-3_14)
- [Expander Graphs (Hoory-Linial-Wigderson)](https://www.cs.huji.ac.il/~nati/PAPERS/expander_survey.pdf)

### SAT Solving
- [Handbook of Satisfiability](https://www.iospress.nl/book/handbook-of-satisfiability-2/)
- [SAT Competition](http://satcompetition.org/)

## Getting Help

### For Technical Issues
- **GitHub Issues**: Bug reports and feature requests
- **GitHub Discussions**: Questions and ideas

### For Lean Questions
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [Lean Community](https://leanprover-community.github.io/)

### For Complexity Theory Questions
- [Theoretical Computer Science Stack Exchange](https://cstheory.stackexchange.com/)
- [Complexity Zulip](https://complexity.zulipchat.com/)

## Frequently Asked Questions

### Q: Is this a complete proof of P ≠ NP?
**A**: No. This is a framework with many `sorry` placeholders. It's a research program, not a finished proof.

### Q: What's the current status?
**A**: Framework complete, empirical validation working, formal proofs in progress. See [PROJECT_STATUS.md](PROJECT_STATUS.md).

### Q: Can I contribute?
**A**: Yes! See [CONTRIBUTING.md](../CONTRIBUTING.md). Areas: proof completion, bound improvement, empirical validation.

### Q: What's the biggest challenge?
**A**: GAP 1 (treewidth to universal limit) and GAP 2 (improving α constant) are the hardest parts.

### Q: How long until completion?
**A**: Realistic estimate: 18-24 months for core proofs, assuming dedicated researchers.

### Q: What if the approach fails?
**A**: Even partial results would be valuable. The formalization effort alone is a contribution to complexity theory and formal methods.

## Version History

- **v0.1.0** (Oct 2025): Initial framework, all gaps outlined, CI/CD setup
- **v0.0.1** (Sep 2025): Repository creation

## License

MIT License - see [LICENSE](../LICENSE) file.

---

**Last Updated**: October 10, 2025  
**Maintainers**: P-NP Framework Contributors
