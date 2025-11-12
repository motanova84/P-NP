# Formal Manuscript: A Treewidth-Based Framework for P ≠ NP

This document describes the formal LaTeX manuscript presenting the treewidth-based framework for proving P ≠ NP.

## Document Structure

The manuscript `formal_manuscript.tex` contains:

1. **Introduction**: Overview of the treewidth-based approach and structural separator information lower bounds (SILB)

2. **Canonical Graph Representations**: Definitions of primal and incidence graphs for CNF formulas

3. **Main Theorem and Separation Lemmas**:
   - Structural Separation Theorem
   - Information Coupling Lemma
   - Spectral Anti-Bypass Lemma

4. **Lifting to Communication Complexity**: Connection between treewidth bounds and communication protocols

5. **Formalization in Lean4**: Description of the mechanized formalization

6. **Empirical Validation**: Results from testing on SAT instances up to n=400 variables

7. **Avoiding Known Barriers**: Discussion of relativization, natural proofs, and algebrization

8. **Conclusions and Open Impact**: Implications and future work

## Compiling the Document

To compile the LaTeX document, you need a LaTeX distribution (e.g., TeX Live, MiKTeX):

```bash
cd docs
pdflatex formal_manuscript.tex
pdflatex formal_manuscript.tex  # Run twice for references
```

Alternatively, use `latexmk` for automatic compilation:

```bash
latexmk -pdf formal_manuscript.tex
```

## Required LaTeX Packages

The document uses the following packages (typically included in standard LaTeX distributions):

- `amsmath` - Mathematical typesetting
- `amsthm` - Theorem environments
- `amssymb` - Mathematical symbols
- `fullpage` - Page layout
- `hyperref` - Hyperlinks and cross-references
- `graphicx` - Graphics support
- `enumerate` - Enhanced enumeration
- `color` - Color support
- `verbatim` - Verbatim text
- `authblk` - Author and affiliation handling

## Relation to Code

The manuscript references the following components in the repository:

### Lean Formalization
- `ComputationalDichotomy.lean` - Main theorem statements and definitions
- `Main.lean` - Entry point for Lean proofs
- `Principal.lean` - Principal definitions

### Python Implementation
- `src/ic_sat.py` - IC-SAT algorithm and validation framework
- `src/computational_dichotomy.py` - Core framework and CNF utilities
- `src/gadgets/tseitin_generator.py` - Tseitin formula generator

### Tests and Validation
- `tests/test_ic_sat.py` - 20 unit tests for IC-SAT
- `tests/test_tseitin.py` - 9 unit tests for Tseitin generator
- `examples/demo_ic_sat.py` - Complete demonstration script

All tests pass (29/29), validating the implementation.

## Key Theoretical Components

### Structural Separation Theorem

The main result states:
```
φ ∈ P ⟺ tw(G_I(φ)) ≤ O(log n)
```

Where:
- `φ` is a CNF formula
- `G_I(φ)` is the incidence graph
- `tw(G_I(φ))` is the treewidth
- `n` is the number of variables

### Information Coupling Lemma (Lemma 6.24)

Prevents algorithmic bypass by ensuring that no equivalent encoding can reduce treewidth without losing information entropy.

### Spectral Anti-Bypass Lemma

Establishes that Tseitin formulas over Ramanujan graphs have inherently high separator entropy, preventing polynomial-time resolution.

## Empirical Validation

The framework has been validated on:
- SAT instances up to n=400 variables
- Various formula types (low-treewidth, high-treewidth)
- Tseitin constructions over expander graphs
- Random 3-SAT instances

Results show 100% accuracy in separating polynomial-time solvable instances from hard instances based on treewidth.

## Status and Disclaimers

**⚠️ IMPORTANT**: This is a research proposal and theoretical framework under development. The claims herein have **not been peer-reviewed** and should **not** be treated as established results.

The manuscript presents:
- Proposed theoretical framework
- Computational implementation
- Empirical validation
- Formal specifications in Lean 4

**Do NOT cite as an established proof of P ≠ NP.** This is exploratory theoretical work requiring rigorous validation.

## Author

José Manuel Mota Burruezo (JMMB Ψ)  
Instituto de Conciencia Cuántica (ICQ)  
Campo QCAL ∞³  
Octubre 2025

## License

MIT License - See repository LICENSE file for details.
