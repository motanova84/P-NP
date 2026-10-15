/-!
# Axiom Documentation

This file documents all axioms used in the P≠NP formal verification,
explaining why each axiom is necessary and what it represents.

## Classification of Axioms

### 1. Foundational Definitions (Cannot be eliminated without graph theory library)

These axioms represent mathematical objects that require full formalization
of graph theory, which is beyond the scope of this project.

* `Graph`: The type of graphs
* `graphTreewidth`: The treewidth function on graphs
* `incidenceGraph`: Maps CNF formulas to their incidence graphs
* `treewidth`: The treewidth of a CNF formula (via its incidence graph)

**Justification**: These require a complete graph theory library including:
- Graph data structures
- Tree decomposition algorithms
- Treewidth computation
- Properties of graph minors

### 2. Communication Complexity Framework

These axioms define the communication complexity model used for lower bounds.

* `Protocol`: The type of communication protocols
* `informationComplexity`: Information complexity measure
* `communicationComplexity`: Communication complexity measure

**Justification**: Full formalization would require:
- Protocol transcript spaces
- Probability distributions over inputs
- Conditional mutual information
- Connection to distributional complexity

### 3. Circuit Complexity

These axioms define Boolean circuits and complexity classes.

* `Circuit`: The type of Boolean circuits
* `size`: The size (number of gates) of a circuit
* `InP`: Membership in the complexity class P
* `InNP`: Membership in the complexity class NP

**Justification**: Full formalization would require:
- Circuit syntax and semantics
- Uniformity conditions
- Time/space resource bounds
- Verifier/certificate models for NP

### 4. Gadget Constructions

These axioms represent specialized graph constructions for lifting theorems.

* `Gadget`: The type of communication gadgets
* `RamanujanGraph`: The type of Ramanujan graphs (optimal expanders)
* `tseitin_gadget`: Construction of Tseitin formulas over expander graphs

**Justification**: Full formalization would require:
- Spectral graph theory
- Eigenvalue bounds
- Explicit constructions of Ramanujan graphs
- Tseitin formula encoding

### 5. Standard Complexity Theory Results

These axioms represent well-established results from complexity theory.

* `SAT_in_NP`: SAT is in NP (standard textbook result)
* `sat_in_np`: Existential witness for SAT in NP
* `treewidthIsGraphTreewidth`: Definition connecting formula and graph treewidth

**Justification**: These are standard results that would require
formalizing entire textbook chapters on complexity theory.

## Reduction Strategy

We have reduced axioms by:

1. **Implementing computable definitions**: All CNF formula operations
   (evaluation, satisfiability) are now fully defined functions.

2. **Proving basic properties**: Properties that follow from definitions
   (like non-negativity of treewidth) are now proven.

3. **Adding partial proofs**: Where full proofs require external libraries,
   we provide proof sketches showing the logical structure.

4. **Clear separation**: We clearly separate what is axiomatized (graph theory,
   communication complexity) from what is proven (formula manipulation,
   logical connections).

## Total Axiom Count

* Foundational (Graph theory): 4 axioms
* Communication complexity: 3 axioms
* Circuit complexity: 4 axioms
* Gadget constructions: 3 axioms
* Standard results: 3 axioms
* Structural properties: 1 axiom (chainHasLowTreewidth)

**Total: 18 axioms** (reduced from original count by implementing definitions)

## Future Work

To eliminate more axioms, the following formalizations would be needed:

1. **mathlib4 graph theory extension**: Complete treewidth formalization
2. **Communication complexity library**: Protocol model and information measures
3. **Circuit complexity library**: Boolean circuits and uniformity
4. **Spectral graph theory**: Ramanujan graphs and expander properties

These are substantial projects beyond the scope of this work, but the
modular structure allows easy replacement of axioms with full definitions
as these libraries become available.

## Verification Strategy

Despite the axioms, the formalization provides value by:

1. **Type-checking**: All theorem statements are well-typed and consistent
2. **Proof structure**: The logical dependencies are made explicit
3. **Proof sketches**: Partial proofs show how full proofs would proceed
4. **Modularity**: Each axiom is isolated and can be replaced independently
5. **Documentation**: Every axiom is justified and explained

This makes the work reviewable by experts and establishes a clear
roadmap for complete mechanization.
-/

namespace AxiomDocumentation

-- This is a documentation-only file with no executable content
-- All axioms are documented in the comment above

end AxiomDocumentation
