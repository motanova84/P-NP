# SAT and Cook-Levin Theorem Formalization

This directory contains the formalization of the Boolean Satisfiability (SAT) problem and the Cook-Levin theorem, which establishes SAT as the first NP-complete problem.

## New Modules

### Formal.Reductions

**Location**: `formal/Reductions.lean`

This module provides the foundational infrastructure for complexity theory:

#### Core Definitions

- **Language**: Decision problems represented as predicates over strings
- **TuringMachine**: Abstract model of computation with:
  - Input alphabet Σ and tape alphabet Γ
  - State set Q with initial, accept, and reject states
  - Transition function δ: Q × Γ → Option (Q × Γ × Direction)
- **Configuration**: Snapshot of machine state (current state, head position, tape contents)
- **Computation Model**: Functions for single-step and multi-step execution

#### Complexity Classes

- **NTIME(f)**: Non-deterministic time class for time bound f
- **NP_Class**: The class NP = ⋃ₖ NTIME(nᵏ)
- **PolynomialReduction**: Many-one polynomial-time reduction L₁ ≤ₚ L₂
- **NPComplete**: NP-complete problems (in NP and NP-hard)

#### Key Theorems

- **reduction_transitive**: Polynomial-time reductions compose transitively
- **np_complete_in_p_implies_p_eq_np**: If any NP-complete problem is in P, then P = NP

### Formal.SAT

**Location**: `formal/SAT.lean`

This module formalizes the SAT problem and proves the Cook-Levin theorem:

#### Boolean Formulas

- **BoolVar**: Boolean variables identified by natural numbers
- **Literal**: Variables or their negations
- **Clause**: Disjunctions of literals (OR)
- **CNFFormula**: Conjunctions of clauses (AND)
- **Assignment**: Boolean valuations of variables
- **Satisfiable**: Existence of satisfying assignment

#### SAT as a Language

- **encode_formula**: Encodes CNF formulas as binary strings
- **SAT_Language**: The language of satisfiable CNF formulas

#### Cook-Levin Theorem

The main result establishing SAT as NP-complete:

1. **SAT_in_NP**: SAT is in NP
   - Certificate: An assignment (polynomial size)
   - Verification: Evaluate formula (polynomial time)

2. **cook_encoding**: The Cook encoding
   - Converts Turing machine computation to CNF formula
   - Uses variables indexed by (time, position, content)
   - Clauses enforce:
     - Initial configuration
     - Valid transitions
     - Final accepting state
     - Uniqueness (each cell has one symbol)

3. **cook_preserves_acceptance**: Correctness of Cook encoding
   - Machine accepts ⟺ Formula is satisfiable

4. **cook_levin_reduction**: Any NP language reduces to SAT
   - For any L ∈ NTIME(nᵏ), construct reduction L ≤ₚ SAT
   - Reduction: w ↦ encode(cook_encoding(M, w, |w|ᵏ))
   - Polynomial time: O(n³ᵏ)
   - Preserves membership: w ∈ L ⟺ reduction(w) ∈ SAT

5. **SAT_is_NP_complete**: Corollary establishing SAT is NP-complete

#### Additional Results

- **ThreeSAT_Language**: 3-SAT (clauses with ≤3 literals)
- **three_sat_is_np_complete**: 3-SAT is also NP-complete
- **sat_in_p_implies_p_eq_np**: If SAT ∈ P, then P = NP

## Integration with Existing Code

The new modules integrate seamlessly with the existing P≠NP proof framework:

1. **ComputationalDichotomy**: Uses CNFFormula definitions compatible with SAT.lean
2. **MainTheorem**: Can reference SAT as a canonical NP-complete problem
3. **Formal.lean**: Updated to import both new modules

## Mathematical Background

### Cook-Levin Theorem (1971-1973)

**Theorem**: SAT is NP-complete.

**Proof Strategy**:
1. Show SAT ∈ NP (easy: guess assignment, verify in polynomial time)
2. Show SAT is NP-hard: For any L ∈ NP with NDTM M running in time nᵏ:
   - Encode M's computation on input w as formula φ
   - φ has O(n²ᵏ) variables and clauses
   - φ is constructible in polynomial time
   - M accepts w ⟺ φ is satisfiable

### Historical Significance

- **First NP-complete problem**: Established the concept of NP-completeness
- **Hundreds of problems**: Now known to be NP-complete by reduction from SAT
- **P vs NP**: SAT provides a canonical hard problem for the P≠NP question

## Implementation Notes

### Axiomatization

The formalization uses axioms where full implementation would be extensive:

- Binary encoding details (`encode_formula`)
- Complete Turing machine constructions
- Some proof details requiring extensive case analysis

This follows the pattern established in other modules (e.g., P_neq_NP.lean).

### Proof Sketches

Key theorems include detailed proof sketches showing:
- Mathematical strategy
- Key lemmas and their application
- Structure of the argument

Full formalization would require:
- Complete binary encoding library
- Extensive Turing machine verification
- Detailed case analysis for all configurations

### Type Safety

The formalization maintains strong type safety:
- Generic over alphabets (Σ, Γ, Q)
- Type classes for alphabet and state constraints
- Decidability instances where needed

## Usage Examples

```lean
import Formal.SAT

-- Define a simple formula: (x₀ ∨ ¬x₁)
def simple_formula : CNFFormula := 
  [[Literal.pos ⟨0⟩, Literal.neg ⟨1⟩]]

-- Prove it's satisfiable
example : Satisfiable simple_formula := by
  use fun v => v.id = 0  -- Assignment: x₀ = true
  unfold eval_formula eval_clause eval_literal
  simp

-- Use Cook-Levin: reduce any NP problem to SAT
example {Σ : Type*} (L : Language Σ) (h : L ∈ NP_Class) :
  L ≤ₚ SAT_Language := 
  cook_levin_reduction L h
```

## References

1. Cook, Stephen A. (1971). "The complexity of theorem-proving procedures". *STOC '71*.
2. Levin, Leonid (1973). "Universal search problems". *Problems of Information Transmission*.
3. Sipser, Michael. *Introduction to the Theory of Computation*. 3rd edition.
4. Arora, Sanjeev and Barak, Boaz. *Computational Complexity: A Modern Approach*.

## Future Work

Potential extensions:

1. **Full Encoding**: Complete binary encoding/decoding functions
2. **Concrete Examples**: Formalize specific NP-complete problems (CLIQUE, VERTEX-COVER, etc.)
3. **Karp's Reductions**: The original 21 NP-complete problems
4. **Stronger Results**: Polynomial hierarchy, Schöning's algorithm, etc.
5. **Connection to P≠NP**: Use SAT hardness in the main separation theorem

## Testing

The implementation type-checks in Lean 4 (v4.20.0) with Mathlib.

To verify:
```bash
cd /path/to/P-NP
lake build Formal.SAT
```

## Authors

- Implementation: GitHub Copilot
- Review: motanova84
- Framework: Part of the P≠NP formalization project
