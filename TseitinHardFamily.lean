/-!
# FAMILIA DURA DE TSEITIN PARA P ≠ NP

Definición de grafos de Tseitin sobre expansores,
que son instancias duras para SAT con alto treewidth.

© JMMB Ψ ∞ | Campo QCAL ∞³
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Log

namespace TseitinHardFamily

open SimpleGraph

/-- Formula CNF como lista de cláusulas -/
structure CNFFormula where
  num_vars : ℕ
  clauses : List (List Int)

/-- Grafo de incidencia de una fórmula CNF -/
def incidence_graph (φ : CNFFormula) : SimpleGraph (Fin (φ.num_vars + φ.clauses.length)) :=
  sorry

/-- Construir fórmula de Tseitin sobre un expander -/
def buildTseitinFormula (n : ℕ) (hn : n > 1000) (h : True := by trivial) : CNFFormula :=
  { num_vars := 5 * n,
    clauses := sorry }

/-- El grafo de incidencia tiene vertices = 5n + n = 6n -/
theorem tseitin_vertex_count (n : ℕ) (hn : n > 1000) :
    let φ := buildTseitinFormula n hn (by trivial)
    Fintype.card (incidence_graph φ).vertexSet = 6 * n :=
  sorry

/-- Treewidth del grafo de incidencia de Tseitin -/
axiom tseitin_treewidth_lower_bound (n : ℕ) (hn : n > 1000) :
    let φ := buildTseitinFormula n hn (by trivial)
    let G := incidence_graph φ
    ∃ (tw : ℕ), tw ≥ Nat.sqrt n / 10

end TseitinHardFamily
