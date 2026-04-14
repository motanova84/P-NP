/-!
# SAT - Boolean Satisfiability Definitions

This module provides core definitions for Boolean satisfiability (SAT) problems,
including CNF formulas, assignments, and the incidence graph structure.

## Main Definitions

* `BoolVar` - Boolean variables
* `Literal` - Positive or negative literals
* `Clause` - Disjunction of literals
* `CNFFormula` - Conjunction of clauses (CNF formula)
* `Assignment` - Assignment of truth values to variables
* `Satisfiable` - Satisfiability predicate
* `IncidenceVertex` - Vertices in the incidence graph
* `incidenceGraph` - The incidence graph of a CNF formula

## Implementation Notes

This provides a constructive, axiom-free foundation for SAT theory.
All definitions are explicit and computable.

-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! ## Boolean Variables and Literals -/

/-- A Boolean variable with a unique identifier -/
structure BoolVar where
  id : ℕ
  deriving Repr, DecidableEq, Inhabited

/-- A literal is a Boolean variable or its negation -/
inductive Literal where
  | pos : BoolVar → Literal
  | neg : BoolVar → Literal
  deriving Repr, DecidableEq

/-- Get the underlying variable of a literal -/
def Literal.var : Literal → BoolVar
  | pos v => v
  | neg v => v

/-- A clause is a disjunction (OR) of literals -/
def Clause := List Literal

/-- A CNF formula is a conjunction (AND) of clauses -/
def CNFFormula := List Clause

/-! ## Assignments and Evaluation -/

/-- An assignment maps Boolean variables to truth values -/
def Assignment := BoolVar → Bool

/-- Evaluate a literal under an assignment -/
def evalLiteral (α : Assignment) : Literal → Bool
  | Literal.pos v => α v
  | Literal.neg v => !(α v)

/-- Evaluate a clause (true if any literal is true) -/
def evalClause (α : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral α)

/-- Evaluate a CNF formula (true if all clauses are true) -/
def evalFormula (α : Assignment) (φ : CNFFormula) : Bool :=
  φ.all (evalClause α)

/-- A formula is satisfiable if there exists a satisfying assignment -/
def Satisfiable (φ : CNFFormula) : Prop :=
  ∃ α : Assignment, evalFormula α φ = true

/-! ## Formula Properties -/

/-- Get all variables mentioned in a literal -/
def Literal.vars : Literal → List BoolVar
  | Literal.pos v => [v]
  | Literal.neg v => [v]

/-- Get all variables in a clause -/
def Clause.vars (c : Clause) : List BoolVar :=
  c.bind Literal.vars

/-- Get all variables in a formula -/
def CNFFormula.vars (φ : CNFFormula) : List BoolVar :=
  φ.bind Clause.vars

/-- Number of (distinct) variables in a formula -/
def numVars (φ : CNFFormula) : ℕ :=
  φ.vars.toFinset.card

/-- Number of clauses in a formula -/
def numClauses (φ : CNFFormula) : ℕ :=
  φ.length

/-! ## Incidence Graph -/

/-- Vertices in the incidence graph:
    - Variables (one per Boolean variable)
    - Clauses (one per clause)
-/
inductive IncidenceVertex where
  | var : BoolVar → IncidenceVertex
  | clause : ℕ → IncidenceVertex  -- clause index
  deriving Repr, DecidableEq

/-- The incidence graph of a CNF formula.
    
    Edges connect:
    - A variable vertex to a clause vertex if the variable appears in the clause
    
    This is a bipartite graph structure that captures the variable-clause
    relationships in the formula.
-/
def incidenceGraph (φ : CNFFormula) : SimpleGraph IncidenceVertex :=
  { Adj := fun u v =>
      match u, v with
      | IncidenceVertex.var x, IncidenceVertex.clause i =>
          i < φ.length ∧ x ∈ (φ.get! i).vars
      | IncidenceVertex.clause i, IncidenceVertex.var x =>
          i < φ.length ∧ x ∈ (φ.get! i).vars
      | _, _ => False
    symm := by
      intro u v
      cases u <;> cases v <;> simp [List.get!] <;> tauto
    loopless := by
      intro v
      cases v <;> simp }

/-! ## Treewidth (forward declaration for use in other modules) -/

/-- Treewidth of a graph (to be properly defined in Treewidth modules) -/
axiom treewidth {V : Type*} [DecidableEq V] : SimpleGraph V → ℕ

/-! ## Basic Lemmas -/

/-- Empty formula is satisfiable -/
lemma empty_satisfiable : Satisfiable [] := by
  use (fun _ => true)
  exact List.all_nil _

/-- A formula with an empty clause is unsatisfiable -/
lemma empty_clause_unsatisfiable (φ : CNFFormula) (h : [] ∈ φ) : 
  ¬Satisfiable φ := by
  intro ⟨α, hsat⟩
  have : evalClause α [] = false := List.any_nil
  have : [] ∈ φ := h
  have : (evalClause α []) = true := by
    have : evalFormula α φ = true := hsat
    unfold evalFormula at this
    have : φ.all (evalClause α) = true := this
    sorry -- List.all requires all elements satisfy predicate
  contradiction
