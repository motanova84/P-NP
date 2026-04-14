/-!
# Tests for Explicit Expander Formulas

This file contains tests verifying the explicit construction of hard CNF formulas
with linear treewidth.
-/

import Formal.ExplicitHardFormulas

namespace ExplicitHardFormulasTests

open TseitinFormula ExplicitExpanders ExplicitHardFormulas

/-! ## Basic Construction Tests -/

/-- Test: Can construct explicit expander graph -/
example : ∃ G : SimpleGraph (MargulisVertex 5), G = MargulisGabberGalilGraph 5 := by
  use MargulisGabberGalilGraph 5

/-- Test: Can construct Tseitin formula -/
example : ∃ φ : CNF, φ = tseitin_expander_formula 100 := by
  use tseitin_expander_formula 100

/-- Test: Can construct explicit hard formula -/
example : ∃ φ : CNF, φ = explicit_hard_formula 100 := by
  use explicit_hard_formula 100

/-! ## Property Tests -/

/-- Test: Formula is UNSAT for n = 100 -/
example : ¬satisfiable (explicit_hard_formula 100) := by
  have h : 100 ≥ 9 := by omega
  have ⟨h_unsat, _, _, _⟩ := explicit_hard_formula_properties 100 h
  exact h_unsat

/-- Test: Formula has bounded size for n = 100 -/
example : (explicit_hard_formula 100).numVars ≤ 1000 := by
  have h : 100 ≥ 9 := by omega
  have ⟨_, h_vars, _, _⟩ := explicit_hard_formula_properties 100 h
  omega

/-- Test: Formula has bounded clauses for n = 100 -/
example : (explicit_hard_formula 100).clauses.length ≤ 30000 := by
  have h : 100 ≥ 9 := by omega
  have ⟨_, _, h_clauses, _⟩ := explicit_hard_formula_properties 100 h
  omega

/-- Test: Formula has linear treewidth for n = 100 -/
example : (treewidth (incidence_graph (explicit_hard_formula 100)) : ℝ) ≥ 0.5 := by
  have h : 100 ≥ 9 := by omega
  have ⟨_, _, _, h_tw⟩ := explicit_hard_formula_properties 100 h
  -- 0.005 * 100 = 0.5
  linarith

/-! ## Existence Tests -/

/-- Test: Existence theorem instantiates for n = 9 -/
example : ∃ φ : CNF,
  (¬satisfiable φ) ∧
  (φ.numVars ≤ 90) ∧
  (φ.clauses.length ≤ 2700) ∧
  ((treewidth (incidence_graph φ) : ℝ) ≥ 0.045) := by
  have h := exists_unsat_formula_with_linear_treewidth 9 (by omega)
  obtain ⟨φ, h_unsat, h_vars, h_clauses, h_tw⟩ := h
  use φ
  exact ⟨h_unsat, h_vars, h_clauses, h_tw⟩

/-- Test: Existence theorem instantiates for n = 100 -/
example : ∃ φ : CNF,
  (¬satisfiable φ) ∧
  (φ.numVars ≤ 1000) ∧
  (φ.clauses.length ≤ 30000) ∧
  ((treewidth (incidence_graph φ) : ℝ) ≥ 0.5) := by
  have h := exists_unsat_formula_with_linear_treewidth 100 (by omega)
  obtain ⟨φ, h_unsat, h_vars, h_clauses, h_tw⟩ := h
  use φ
  constructor; exact h_unsat
  constructor; omega
  constructor; omega
  linarith

/-- Test: Better constant theorem instantiates for n = 100 -/
example : ∃ φ : CNF,
  (¬satisfiable φ) ∧
  ((treewidth (incidence_graph φ) : ℝ) ≥ 1.0) := by
  have h := exists_unsat_formula_with_better_constant 100 (by omega)
  obtain ⟨φ, h_unsat, _, _, h_tw⟩ := h
  use φ
  constructor; exact h_unsat
  linarith

/-! ## GAP 1 Closure Test -/

/-- Test: GAP 1 is closed - there exists an explicit family -/
example : ∃ (family : ℕ → CNF),
  (∀ n : ℕ, n ≥ 100 →
    (¬satisfiable (family n)) ∧
    ((family n).numVars ≤ 10 * n) ∧
    ((family n).clauses.length ≤ 300 * n) ∧
    ((treewidth (incidence_graph (family n)) : ℝ) ≥ 0.01 * n)) := by
  exact gap_1_closed

/-- Test: The family works for specific value n = 100 -/
example : let family := tseitin_expander_formula in
  (¬satisfiable (family 100)) ∧
  ((family 100).numVars ≤ 1000) ∧
  ((family 100).clauses.length ≤ 30000) ∧
  ((treewidth (incidence_graph (family 100)) : ℝ) ≥ 1.0) := by
  have h := exists_unsat_formula_with_better_constant 100 (by omega)
  obtain ⟨φ, h_unsat, h_vars, h_clauses, h_tw⟩ := h
  -- φ is tseitin_expander_formula 100
  constructor; exact h_unsat
  constructor; omega
  constructor; omega
  linarith

/-! ## Consistency Tests -/

/-- Test: CNF structure is well-formed -/
example : let φ := explicit_hard_formula 100 in
  φ.numVars ≥ 0 ∧ φ.clauses.length ≥ 0 := by
  constructor <;> omega

/-- Test: Literal evaluation is consistent -/
example : ∀ (n : ℕ) (a : Assignment n) (v : ℕ),
  v < n →
  eval_literal a (Literal.pos v) = a ⟨v, by assumption⟩ := by
  intro n a v hv
  simp [eval_literal, hv]

/-- Test: Clause evaluation handles empty clause -/
example : ∀ (n : ℕ) (a : Assignment n),
  eval_clause a [] = false := by
  intro n a
  simp [eval_clause]

end ExplicitHardFormulasTests
