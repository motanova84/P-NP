/-
  Basic definitions for CNF formulas, protocols, and complexity measures
-/

-- CNF formula type
structure CNF where
  variables : ℕ
  clauses : List (List Int)

-- Protocol type
structure Protocol where
  rounds : ℕ
  communication : ℕ

-- RAM algorithm type
structure RAM_Algorithm where
  time : ℕ
  space : ℕ

-- Complexity measures
def Time (A : RAM_Algorithm) : ℕ := A.time
def Comm (Π : Protocol) : ℕ := Π.communication

-- Information Complexity placeholder
axiom IC : Protocol → ℕ → ℕ

-- Treewidth placeholder
axiom tw : CNF → ℕ

-- Graph incidence structure
axiom G_I : CNF → Type

-- Communication problem types
axiom DISJₖ : ℕ → Type
axiom compose : (ℕ → Type) → Type → Type

notation "DISJₖ ∘ " g => compose (DISJₖ k) g

-- SAT decision
def is_SAT (φ : CNF) : Prop := sorry

-- Expander Tseitin padding
def expander_tseitin_padding (φ : CNF) : CNF := sorry

-- Separator for information complexity
structure Separator where
  size : ℕ
  structure : List ℕ
