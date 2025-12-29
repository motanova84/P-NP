/-!
# Examples for the Seven Stairs Implementation

This file contains concrete examples demonstrating the usage of the Seven Stairs
formalization in `SevenStairs.lean`.

-/

import SevenStairs

namespace SevenStairsExamples

-- ═══════════════════════════════════════════════════════════════
-- Example 1: Simple CNF Formula
-- ═══════════════════════════════════════════════════════════════

/-- Example formula: (x₁ ∨ ¬x₂) ∧ (x₂ ∨ x₃) ∧ (¬x₁ ∨ ¬x₃)
    
    This is a satisfiable 3-CNF formula with 3 variables and 3 clauses.
-/
def example_formula : CnfFormula ℕ :=
  CnfFormula.mk {
    -- Clause 1: x₁ ∨ ¬x₂
    Clause.mk {Literal.pos 1, Literal.neg 2},
    -- Clause 2: x₂ ∨ x₃
    Clause.mk {Literal.pos 2, Literal.pos 3},
    -- Clause 3: ¬x₁ ∨ ¬x₃
    Clause.mk {Literal.neg 1, Literal.neg 3}
  }

/-- Extract variables from the example formula -/
#check formula_vars example_formula
-- Expected: Finset ℕ containing {1, 2, 3}

/-- The example formula is satisfiable -/
example : Satisfiable example_formula := by
  -- Assignment: x₁ = true, x₂ = true, x₃ = false
  use fun n => n ≤ 2
  -- Under this assignment:
  -- Clause 1: true ∨ ¬true = true ∨ false = true ✓
  -- Clause 2: true ∨ false = true ✓
  -- Clause 3: ¬true ∨ ¬false = false ∨ true = true ✓
  simp [cnf_eval, clause_eval, literal_eval]
  sorry -- Detailed evaluation proof

-- ═══════════════════════════════════════════════════════════════
-- Example 2: Unsatisfiable Formula
-- ═══════════════════════════════════════════════════════════════

/-- Example unsatisfiable formula: (x₁) ∧ (¬x₁)
    
    This formula is clearly unsatisfiable.
-/
def unsat_formula : CnfFormula ℕ :=
  CnfFormula.mk {
    Clause.mk {Literal.pos 1},
    Clause.mk {Literal.neg 1}
  }

/-- The unsatisfiable formula is indeed unsatisfiable -/
example : ¬Satisfiable unsat_formula := by
  intro ⟨assignment, h⟩
  -- If x₁ is true, second clause fails
  -- If x₁ is false, first clause fails
  simp [cnf_eval, clause_eval, literal_eval] at h
  sorry -- Detailed unsatisfiability proof

-- ═══════════════════════════════════════════════════════════════
-- Example 3: Incidence Graph Construction
-- ═══════════════════════════════════════════════════════════════

/-- The incidence graph of the example formula -/
def example_graph : SimpleGraph ℕ := incidenceGraph example_formula

/-- The incidence graph has the symmetry property -/
example : Symmetric example_graph.Adj := example_graph.symm

/-- The incidence graph is loopless -/
example : Irreflexive example_graph.Adj := example_graph.loopless

/-- Verify specific edges in the incidence graph -/
example : example_graph.Adj 1 2 := by
  -- Variables 1 and 2 both appear in Clause 1: (x₁ ∨ ¬x₂)
  simp [example_graph, incidenceGraph]
  constructor
  · norm_num
  · use Clause.mk {Literal.pos 1, Literal.neg 2}
    constructor
    · simp [example_formula]
    · use Literal.pos 1
      constructor
      · simp [Clause.literals]
      · use Literal.neg 2
        constructor
        · simp [Clause.literals]
        · sorry -- Complete edge proof

-- ═══════════════════════════════════════════════════════════════
-- Example 4: Variable Extraction
-- ═══════════════════════════════════════════════════════════════

/-- Formula with 5 variables -/
def large_formula : CnfFormula ℕ :=
  CnfFormula.mk {
    Clause.mk {Literal.pos 1, Literal.pos 2, Literal.neg 3},
    Clause.mk {Literal.neg 2, Literal.pos 4},
    Clause.mk {Literal.pos 3, Literal.neg 5},
    Clause.mk {Literal.pos 5, Literal.neg 1}
  }

/-- The large formula has exactly 5 variables -/
example : (formula_vars large_formula).card = 5 := by
  simp [formula_vars, large_formula]
  sorry -- Card computation

-- ═══════════════════════════════════════════════════════════════
-- Example 5: Spectral Properties (for illustration)
-- ═══════════════════════════════════════════════════════════════

section SpectralExample

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Example: κ_π is positive for non-trivial graphs -/
example (G : SimpleGraph V) (h : ∃ u v, G.Adj u v) : kappa_pi G ≥ 0 := by
  simp [kappa_pi]
  sorry -- Spectral gap positivity

end SpectralExample

-- ═══════════════════════════════════════════════════════════════
-- Example 6: Satisfiability Checking
-- ═══════════════════════════════════════════════════════════════

/-- A tautological formula: (x ∨ ¬x) for any x -/
def tautology : CnfFormula ℕ :=
  CnfFormula.mk {
    Clause.mk {Literal.pos 1, Literal.neg 1}
  }

/-- Tautologies are satisfiable -/
example : Satisfiable tautology := by
  use fun _ => true  -- Any assignment works
  simp [cnf_eval, clause_eval, literal_eval, tautology]
  sorry -- Tautology proof

-- ═══════════════════════════════════════════════════════════════
-- Example 7: Empty and Trivial Cases
-- ═══════════════════════════════════════════════════════════════

/-- Empty formula (no clauses) -/
def empty_formula : CnfFormula ℕ :=
  CnfFormula.mk ∅

/-- Empty formula is satisfiable (vacuously true) -/
example : Satisfiable empty_formula := by
  use fun _ => true
  simp [cnf_eval, empty_formula]

/-- Formula with empty clause is unsatisfiable -/
def empty_clause_formula : CnfFormula ℕ :=
  CnfFormula.mk {
    Clause.mk ∅  -- Empty clause (always false)
  }

/-- Formula with empty clause is unsatisfiable -/
example : ¬Satisfiable empty_clause_formula := by
  intro ⟨assignment, h⟩
  -- Empty clause evaluates to false for any assignment
  simp [cnf_eval, clause_eval, empty_clause_formula] at h

end SevenStairsExamples

/-!
## Summary of Examples

These examples demonstrate:

1. **Construction**: How to build CNF formulas using the inductive types
2. **Variables**: How to extract variable sets using `formula_vars`
3. **Evaluation**: How to evaluate formulas and check satisfiability
4. **Incidence Graph**: How to construct and reason about incidence graphs
5. **Properties**: Basic properties like symmetry and looplessness
6. **Edge Cases**: Empty formulas, tautologies, unsatisfiable formulas

All examples use the constructive definitions from `SevenStairs.lean`.
-/
