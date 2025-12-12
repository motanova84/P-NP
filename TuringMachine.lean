/-! # Turing Machine Definitions

Basic definitions for Turing machines used in complexity theory.

-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

-- ══════════════════════════════════════════════════════════════
-- ALFABETOS Y SÍMBOLOS
-- ══════════════════════════════════════════════════════════════

/-- Typeclass for input alphabet embedded in tape alphabet -/
class InputAlphabet (Σ Γ : Type*) where
  /-- Injection from input alphabet to tape alphabet -/
  input_subset : Σ → Γ

/-- Typeclass for state set with special states -/
class StateSet (Q : Type*) where
  /-- Starting state -/
  start : Q
  /-- Accepting state -/
  accept : Q
  /-- Rejecting state -/
  reject : Q

-- ══════════════════════════════════════════════════════════════
-- CINTA DE TURING
-- ══════════════════════════════════════════════════════════════

/-- Tape alphabet with a designated blank symbol -/
class TapeAlphabet (Γ : Type*) where
  /-- The blank symbol -/
  blank : Γ

/-- Direction of tape head movement -/
inductive Direction where
  | left : Direction
  | right : Direction
  | stay : Direction

/-- Turing machine tape -/
structure Tape (Γ : Type*) where
  /-- Symbols to the left of the head (stored in reverse order) -/
  left : List Γ
  /-- Symbol under the head -/
  current : Γ
  /-- Symbols to the right of the head -/
  right : List Γ

namespace Tape

variable {Γ : Type*} [TapeAlphabet Γ]

/-- Write a symbol at the current position -/
def write (t : Tape Γ) (γ : Γ) : Tape Γ :=
  { t with current := γ }

/-- Move the tape head -/
def move (t : Tape Γ) (d : Direction) : Tape Γ :=
  match d with
  | Direction.left =>
      match t.left with
      | [] => { left := [], current := TapeAlphabet.blank, right := t.current :: t.right }
      | h :: tl => { left := tl, current := h, right := t.current :: t.right }
  | Direction.right =>
      match t.right with
      | [] => { left := t.current :: t.left, current := TapeAlphabet.blank, right := [] }
      | h :: tl => { left := t.current :: t.left, current := h, right := tl }
  | Direction.stay => t

end Tape

-- ══════════════════════════════════════════════════════════════
-- CONFIGURACIÓN DE MÁQUINA
-- ══════════════════════════════════════════════════════════════

/-- Configuration of a Turing machine -/
structure Config (Σ Γ Q : Type*) [InputAlphabet Σ Γ] [StateSet Q] where
  /-- Current state -/
  state : Q
  /-- Current tape -/
  tape : Tape Γ

-- ══════════════════════════════════════════════════════════════
-- MÁQUINA DE TURING DETERMINISTA
-- ══════════════════════════════════════════════════════════════

/-- Deterministic Turing Machine -/
structure TuringMachine (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  /-- Transition function: Q × Γ → Q × Γ × Direction -/
  δ : Q → Γ → Q × Γ × Direction
  /-- The halting states have no effect on transitions -/
  halt_no_change : ∀ γ : Γ,
    δ StateSet.accept γ = (StateSet.accept, γ, Direction.stay) ∧
    δ StateSet.reject γ = (StateSet.reject, γ, Direction.stay)

-- ══════════════════════════════════════════════════════════════
-- LENGUAJES Y DECISIÓN
-- ══════════════════════════════════════════════════════════════

/-- A language over alphabet Σ is a predicate on strings -/
def Language (Σ : Type*) := List Σ → Prop

/-- A machine decides a language in time bounded by f -/
def DecidesInTime {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (L : Language Σ) (f : ℕ → ℕ) : Prop :=
  ∀ w : List Σ, ∃ t : ℕ, t ≤ f w.length ∧
    -- Machine accepts if and only if w is in the language
    (L w ↔ sorry) ∧  -- Would need to define the execution semantics
    -- Machine halts within time t
    sorry  -- Would need to define halting predicate
