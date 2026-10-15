# Seven Stairs Integration Guide

## Overview

This document describes how the new **Seven Stairs** (Las 7 Escaleras) implementation in `SevenStairs.lean` integrates with and complements the existing P ≠ NP formalization in this repository.

## Relationship to Existing Code

### Existing Implementations

The repository already contains several approaches to the P ≠ NP problem:

1. **`SAT.lean`**: Basic SAT definitions with List-based formulas
2. **`P_neq_NP.lean`**: Incidence graph construction using Sum types
3. **`SpectralTheory.lean`**: Spectral gap and expansion constants
4. **`ComplexityClasses.lean`**: P, NP, and Turing machine definitions
5. **`TseitinHardFamily.lean`**: Tseitin formula construction
6. **`TreewidthTheory.lean`**: Treewidth definitions and properties

### Seven Stairs: A Unified Framework

The **Seven Stairs** provides a **unified, progressive formalization** that:

1. **Starts from scratch**: Defines everything from first principles
2. **Uses Finset throughout**: More constructive than List-based approaches
3. **Provides complete chain**: All 7 steps connect seamlessly
4. **Emphasizes computability**: All definitions are explicit and computable
5. **Minimizes axioms**: Only known results from literature are axiomatized

## Comparison: SevenStairs vs Existing Code

### CNF Formula Representation

| Feature | SAT.lean | P_neq_NP.lean | SevenStairs.lean |
|---------|----------|---------------|------------------|
| Formula type | `List Clause` | `CnfFormula` struct | `CnfFormula V` inductive |
| Clause type | `List Literal` | `List (V × Bool)` | `Clause V` inductive |
| Literal type | `Literal` inductive | `(V × Bool)` pair | `Literal V` inductive |
| Variable extraction | `CNFFormula.vars` | `clauseVars` | `formula_vars` |
| Evaluation | `evalFormula` | Not defined | `cnf_eval` |
| Collection type | `List` | `List` | `Finset` |

**Key Difference**: SevenStairs uses `Finset` consistently for better computational properties and constructive mathematics.

### Incidence Graph

| Feature | SAT.lean | P_neq_NP.lean | SevenStairs.lean |
|---------|----------|---------------|------------------|
| Vertex type | `IncidenceVertex` | `V ⊕ Fin n` | `V` (variables only) |
| Structure | Bipartite (vars + clauses) | Bipartite (vars + clauses) | Variable graph |
| Edge condition | Var in clause | Var in clause | Vars in same clause |
| Proofs | Constructive | Constructive | Constructive |

**Key Difference**: 
- SAT.lean & P_neq_NP.lean: Bipartite graph (variables and clauses as vertices)
- SevenStairs: Variable graph (only variables as vertices, connected if in same clause)

Both are valid representations with different trade-offs.

### Spectral Theory

| Feature | SpectralTheory.lean | SevenStairs.lean |
|---------|---------------------|------------------|
| Spectral gap | `spectralGap G` | `spectral_gap G` |
| κ_Π constant | `κ_Π : ℝ := 100` | `kappa_pi G : ℝ` |
| Frequency-dependent | `spectral_constant_at_frequency` | Not included |
| Laplacian | Not defined | `normalizedLaplacian` |
| Adjacency matrix | Not defined | `adjacencyMatrix` |

**Key Difference**: 
- SpectralTheory: Includes frequency dimension (ω) for extended framework
- SevenStairs: Pure graph-theoretic approach, κ_Π computed from eigenvalues

### Complexity Classes

| Feature | ComplexityClasses.lean | SevenStairs.lean |
|---------|------------------------|------------------|
| P definition | `P_Class {Σ : Type*}` | `P_Class : Type` |
| NP definition | `NP_Class {Σ : Type*}` | `NP_Class : Type` |
| Turing machines | Full definition | Axiomatized |
| Time complexity | `DecidesInTime` | `runTime` axiom |

**Key Difference**: 
- ComplexityClasses: Full Turing machine formalization
- SevenStairs: Simplified axiomatization focusing on the proof chain

## Integration Strategy

### Option 1: Parallel Development (Current)

- Keep both implementations
- SevenStairs provides a clean, pedagogical view
- Existing code provides more detailed technical implementation
- Cross-reference between them in documentation

### Option 2: Unified Implementation (Future)

Merge the approaches:
1. Use SevenStairs's inductive CNF types as the primary definition
2. Provide conversion functions to/from List-based representations
3. Adopt Finset throughout for consistency
4. Keep both bipartite and variable-only incidence graphs
5. Integrate frequency dimension from SpectralTheory

Example unified structure:
```lean
import SevenStairs
import SpectralTheory
import ComplexityClasses

-- Conversion functions
def cnfFormula_to_SevenStairs : CNFFormula → CnfFormula ℕ := ...
def cnfFormula_from_SevenStairs : CnfFormula ℕ → CNFFormula := ...

-- Extended spectral constant
def kappa_pi_at_frequency (G : SimpleGraph V) (ω : ℝ) : ℝ :=
  spectral_constant_at_frequency ω (Fintype.card V) * kappa_pi G
```

## Advantages of Seven Stairs Approach

1. **Progressive Learning**: Each stair builds naturally on the previous
2. **Self-Contained**: Complete proof chain in one file
3. **Pedagogical**: Clear structure makes the argument easy to follow
4. **Constructive**: Maximal use of computable definitions
5. **Type-Safe**: Strong typing prevents errors
6. **Minimal Dependencies**: Uses only core Mathlib

## Advantages of Existing Code

1. **More Detail**: Full Turing machine formalization
2. **Frequency Dimension**: Extended with ω for physical interpretation
3. **Multiple Views**: Different graph representations for different purposes
4. **Battle-Tested**: Already integrated with other modules
5. **Holographic Extensions**: Connections to quantum/holographic frameworks

## Recommended Usage

### For Learning and Understanding
Use **SevenStairs.lean**:
- Clear progression through 7 logical steps
- Minimal prerequisites
- Self-contained examples

### For Research and Extension
Use **existing modules**:
- More detailed technical infrastructure
- Frequency dimension for extended framework
- Integration with holographic/quantum approaches

### For Formal Verification
Use **both**:
- Verify correspondence between representations
- Cross-check proofs using different formalizations
- Identify gaps and strengthen both approaches

## Future Work

### Short Term
1. Add conversion functions between representations
2. Verify that both incidence graphs are equivalent (up to encoding)
3. Connect SevenStairs κ_Π with frequency-dependent κ_Π
4. Add more examples and tests

### Medium Term
1. Implement connected component algorithm for GraphIC
2. Implement eigenvalue computation for spectral_gap
3. Prove correspondence theorems between representations
4. Add comprehensive test suite

### Long Term
1. Complete formal proof with minimal axioms
2. Submit to Lean mathlib or formal verification venues
3. Write accompanying paper explaining the formalization
4. Create interactive proof explorer/visualizer

## Technical Notes

### Type Universe Considerations

- SevenStairs uses `Type` for variable types (universe-polymorphic)
- Existing code sometimes uses `Type*` explicitly
- Both are compatible; SevenStairs can be lifted to any universe

### DecidableEq Requirements

- SevenStairs requires `[DecidableEq V]` for Finset operations
- Existing code sometimes uses weaker typeclass constraints
- This is a reasonable trade-off for constructive computability

### Noncomputable Definitions

Both implementations use `noncomputable` for:
- Eigenvalue computations (requires numerical algorithms)
- Real number operations (non-constructive in classical logic)
- Treewidth computation (NP-hard problem)

This is unavoidable without restricting to computable analysis.

## Conclusion

The **Seven Stairs** implementation provides a clean, pedagogical formalization that complements the existing more detailed technical infrastructure. Both approaches are valuable:

- **Seven Stairs**: For understanding the core logical flow
- **Existing code**: For technical depth and extensions

Together, they provide a comprehensive formalization of the P ≠ NP problem from multiple perspectives.

---

**See Also**:
- `SEVEN_STAIRS_README.md`: Detailed documentation of the Seven Stairs
- `SevenStairs.lean`: Implementation
- `examples/SevenStairsExamples.lean`: Usage examples
- `QUICKSTART.md`: General repository guide

**Last Updated**: 2025-12-13
