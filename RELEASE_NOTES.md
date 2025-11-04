# Release Notes

## v0.2.0 (2025-10-30)

### P≠NP Framework Updates

#### Documentation Enhancements

- **Anti-barriers Section Added**: Expanded "Avoiding Known Barriers" section (now "Anti-Barriers") in `docs/formal_manuscript.tex` with detailed explanations of why the SILB approach avoids three major complexity theory barriers:
  - **Non-relativization**: Separator structure depends on explicit graph topology, not oracle access patterns
  - **Non-natural proofs**: Predicates are neither dense nor efficiently constructible, depend on specific Tseitin gadget constructions
  - **Non-algebrization**: Monotonicity of separator information breaks in polynomial quotient rings

- **Technical Route**: Documented complete proof pipeline:
  1. Treewidth characterization → balanced separators
  2. Communication protocol embedding with information flow
  3. Lifting with explicit Tseitin gadgets over Ramanujan graphs
  4. Circuit lower bounds via standard lifting theorems

#### Formal Methods

- **Lean Formalization Stubs**: Created modular Lean 4 formalization structure:
  - `formal/Treewidth/SeparatorInfo.lean`: SILB lemma stubs
  - `formal/Lifting/Gadgets.lean`: Gadget validity and lifting theorems
  - `formal/LowerBounds/Circuits.lean`: Circuit lower bounds and P≠NP separation

Each module includes:
  - Clear documentation of main results
  - Type signatures for key theorems
  - Implementation notes on proof requirements
  - Relevant references

#### Build System

- **Makefile**: Added comprehensive build automation:
  - `make pdf`: Builds LaTeX document with latexmk
  - `make figs`: Generates figures (when scripts available)
  - `make tables`: Generates tables (when scripts available)
  - `make clean`: Removes build artifacts
  - `make all`: Complete build pipeline

- **Bibliography Management**: Migrated from manual bibliography to biblatex/biber:
  - Added `docs/refs.bib` with structured BibTeX entries
  - Updated LaTeX preamble with biblatex configuration
  - Set `backend=biber`, `style=alphabetic`, `maxbibnames=99`
  - Added references for Razborov-Rudich and Aaronson-Wigderson

### Repository Improvements

- **Modular Structure**: Organized Lean formalization into logical subdirectories
- **Documentation**: Enhanced manuscript with precise technical terminology
- **Reproducibility**: Build system supports automated document generation

### Technical Notes

- All Lean stubs use `sorry` placeholders for proofs to be completed
- LaTeX document requires `latexmk` and `biber` for compilation
- Formalization structure designed for incremental proof development

### Future Work

- Complete Lean proofs for SILB lemma
- Implement Ramanujan graph constructions
- Formalize lifting theorems with full type specifications
- Add computational verification scripts for figures and tables

---

## v0.1.0 (Initial Release)

- Initial framework for P≠NP via treewidth and information complexity
- Python implementation of IC-SAT algorithm
- Basic Lean formalization
- Empirical validation on instances up to n=400
- Documentation and examples
