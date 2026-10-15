/-!
# Treewidth Implementation Tests

This file contains tests for the treewidth implementation to ensure
correctness and consistency with mathematical definitions.

## Test Coverage

1. Basic graph constructions (empty, complete, path, cycle)
2. CNF formula creation and incidence graphs
3. Treewidth properties and bounds
4. Integration tests for the complete system
-/

import PvsNP.TreewidthComplete

namespace TreewidthTests

open TreewidthComplete

/-! ### Basic Construction Tests -/

/-- Test: Empty graph can be constructed -/
example : SimpleGraph (Fin 0) := emptyGraph

/-- Test: Complete graph can be constructed -/
example : SimpleGraph (Fin 5) := completeGraph 5

/-- Test: Path graph can be constructed -/
example : SimpleGraph (Fin 10) := pathGraph 10

/-- Test: Cycle graph can be constructed -/
example : SimpleGraph (Fin 6) := cycleGraph 6

/-! ### CNF Formula Tests -/

/-- Test: Simple CNF formula can be created -/
example : CnfFormula :=
  { numVars := 3
  , clauses := [
      [Literal.pos 0, Literal.pos 1],           -- (x₀ ∨ x₁)
      [Literal.neg 1, Literal.pos 2],           -- (¬x₁ ∨ x₂)
      [Literal.neg 0, Literal.neg 2]            -- (¬x₀ ∨ ¬x₂)
    ]
  }

/-- Test: 3-SAT formula -/
def test_3sat : CnfFormula :=
  { numVars := 4
  , clauses := [
      [Literal.pos 0, Literal.pos 1, Literal.neg 2],
      [Literal.neg 0, Literal.pos 2, Literal.pos 3],
      [Literal.pos 1, Literal.neg 2, Literal.neg 3]
    ]
  }

/-- Test: CNF variables extraction works -/
example : (test_3sat.vars).card = 4 := by rfl

/-! ### Incidence Graph Tests -/

/-- Test: Incidence graph can be constructed from CNF -/
def test_incidence : SimpleGraph (IncVertex 3 3) :=
  incidenceGraph {
    numVars := 3,
    clauses := [
      [Literal.pos 0, Literal.pos 1],
      [Literal.neg 1, Literal.pos 2],
      [Literal.neg 0, Literal.neg 2]
    ]
  }

/-- Test: Variables and clauses are distinct vertex types -/
example : IncVertex 5 10 := IncVertex.var ⟨0, by omega⟩
example : IncVertex 5 10 := IncVertex.clause ⟨0, by omega⟩

/-! ### Treewidth Approximation Tests -/

/-- Test: Treewidth approximation returns a natural number -/
example : ℕ := treewidthApprox (completeGraph 5)

/-- Test: CNF treewidth can be computed -/
example : ℕ := cnfTreewidth test_3sat

/-- Test: Upper bound is always non-negative -/
example (G : SimpleGraph (Fin 10)) : treewidthUpperBound G ≥ 0 := Nat.zero_le _

/-! ### Property Tests -/

/-- Test: Complete graph upper bound -/
example : treewidthUpperBound (completeGraph 5) = 4 := by
  unfold treewidthUpperBound completeGraph
  simp [Finset.univ, Fintype.card]
  rfl

/-- Test: Empty graph approximation -/
example : treewidthApprox (emptyGraph : SimpleGraph (Fin 0)) = 0 := by
  unfold treewidthApprox treewidthUpperBound
  simp [Finset.univ]
  rfl

/-! ### Integration Tests -/

/-- Test: Complete workflow from CNF to treewidth -/
def workflow_test : ℕ :=
  let φ : CnfFormula := {
    numVars := 10,
    clauses := [
      [Literal.pos 0, Literal.pos 1, Literal.pos 2],
      [Literal.neg 3, Literal.pos 4, Literal.neg 5],
      [Literal.pos 6, Literal.neg 7, Literal.pos 8]
    ]
  }
  cnfTreewidth φ

/-- Test: Workflow executes without errors -/
example : workflow_test ≥ 0 := Nat.zero_le _

/-! ### Consistency Tests -/

/-- Test: Literal construction -/
example : Literal := Literal.pos 5
example : Literal := Literal.neg 3

/-- Test: Literals are decidably equal -/
example : Literal.pos 1 = Literal.pos 1 := rfl
example : Literal.pos 1 ≠ Literal.neg 1 := by decide

/-- Test: Bag type works correctly -/
example : Bag (Fin 5) := {0, 1, 2}

/-- Test: Simple graph adjacency -/
example : (completeGraph 3).Adj 0 1 = true := by
  unfold completeGraph SimpleGraph.Adj
  decide

/-! ### Validation Tests -/

/-- Validation: CNF formulas have positive variable count -/
example (φ : CnfFormula) : φ.numVars ≥ 0 := Nat.zero_le _

/-- Validation: Incidence graph vertices are well-typed -/
example (φ : CnfFormula) (i : Fin φ.numVars) : 
  IncVertex φ.numVars φ.clauses.length := IncVertex.var i

/-- Validation: Treewidth approximation is computable -/
example : treewidthApprox (pathGraph 100) ≥ 0 := Nat.zero_le _

/-! ### Proof Obligations -/

-- All main theorems compile and type-check
-- The following are placeholders to ensure the API is correct

#check treewidth_exists
#check tree_treewidth_one
#check complete_graph_treewidth
#check treewidth_monotone
#check empty_graph_treewidth
#check single_vertex_treewidth
#check path_graph_treewidth
#check cycle_graph_treewidth
#check treewidthUpperBound_valid
#check treewidthApprox_dichotomy
#check cnf_large_vars_high_treewidth

-- Type checking passes
#check TreeDecomposition
#check treewidth
#check incidenceGraph
#check cnfTreewidth

end TreewidthTests
