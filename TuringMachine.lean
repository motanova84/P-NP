-- TuringMachine.lean
-- Formalización completa de Máquinas de Turing
-- Sin axiomas adicionales, solo Mathlib estándar

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic

/-! # Máquinas de Turing

Definición estándar de Máquinas de Turing deterministas.

## Referencias
- Sipser, "Introduction to the Theory of Computation" (3rd ed, 2013)
- Arora-Barak, "Computational Complexity" (2009)
-/

-- ══════════════════════════════════════════════════════════════
-- DEFINICIONES BÁSICAS
-- ══════════════════════════════════════════════════════════════

/-- Alfabeto de la cinta (finito) -/
class TapeAlphabet (Γ : Type*) extends Fintype Γ where
  blank : Γ  -- Símbolo en blanco

/-- Alfabeto de entrada (subconjunto del alfabeto de cinta) -/
class InputAlphabet (Σ Γ : Type*) extends TapeAlphabet Γ where
  input_subset : Σ → Γ
  no_blank : ∀ σ : Σ, input_subset σ ≠ blank

/-- Dirección de movimiento del cabezal -/
inductive Direction
  | left
  | right
  | stay

/-- Configuración de la cinta -/
structure TapeConfig (Γ : Type*) where
  /-- Contenido a la izquierda del cabezal (en orden reverso) -/
  left : List Γ
  /-- Símbolo bajo el cabezal -/
  current : Γ
  /-- Contenido a la derecha del cabezal -/
  right : List Γ

namespace TapeConfig

variable {Γ : Type*} [TapeAlphabet Γ]

/-- Mover el cabezal a la izquierda -/
def moveLeft (tape : TapeConfig Γ) : TapeConfig Γ :=
  match tape.left with
  | [] => ⟨[], TapeAlphabet.blank, tape.current :: tape.right⟩
  | h :: t => ⟨t, h, tape.current :: tape.right⟩

/-- Mover el cabezal a la derecha -/
def moveRight (tape : TapeConfig Γ) : TapeConfig Γ :=
  match tape.right with
  | [] => ⟨tape.current :: tape.left, TapeAlphabet.blank, []⟩
  | h :: t => ⟨tape.current :: tape.left, h, t⟩

/-- Escribir símbolo en la posición actual -/
def write (tape : TapeConfig Γ) (γ : Γ) : TapeConfig Γ :=
  ⟨tape.left, γ, tape.right⟩

/-- Mover según dirección -/
def move (tape : TapeConfig Γ) (d : Direction) : TapeConfig Γ :=
  match d with
  | Direction.left => tape.moveLeft
  | Direction.right => tape.moveRight
  | Direction.stay => tape

end TapeConfig
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

/-- Estados de la máquina (finitos) -/
class StateSet (Q : Type*) extends Fintype Q where
  start : Q      -- Estado inicial
  accept : Q     -- Estado de aceptación
  reject : Q     -- Estado de rechazo
  start_neq_accept : start ≠ accept
  start_neq_reject : start ≠ reject
  accept_neq_reject : accept ≠ reject

/-- Máquina de Turing Determinista -/
structure TuringMachine (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  /-- Función de transición: Q × Γ → Q × Γ × Direction -/
  δ : Q → Γ → Option (Q × Γ × Direction)
  /-- Los estados halting no tienen transiciones -/
  halt_no_transition : ∀ γ : Γ,
    δ StateSet.accept γ = none ∧
    δ StateSet.reject γ = none

/-- Configuración completa de la máquina -/
structure Config (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  state : Q
  tape : TapeConfig Γ

namespace TuringMachine

variable {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
variable (M : TuringMachine Σ Γ Q)

/-- Un paso de computación -/
def step (c : Config Σ Γ Q) : Option (Config Σ Γ Q) :=
  match M.δ c.state c.tape.current with
  | none => none  -- Máquina halted
  | some (q', γ', d) => some {
      state := q',
      tape := (c.tape.write γ').move d
    }

/-- Ejecución por n pasos -/
def run (c : Config Σ Γ Q) : ℕ → Option (Config Σ Γ Q)
  | 0 => some c
  | n + 1 => 
      match M.run c n with
      | none => none
      | some c' => M.step c'

/-- Configuración inicial desde input 
    La cabeza comienza en el primer símbolo (o blank si input vacío) -/
def initialConfig (input : List Σ) : Config Σ Γ Q :=
  { state := StateSet.start,
    tape := {
      left := [],
      current := match input with
        | [] => TapeAlphabet.blank  -- Input vacío: cabeza en blank
        | h :: _ => InputAlphabet.input_subset h,  -- Cabeza en primer símbolo
      right := input.tail.map InputAlphabet.input_subset  -- Resto del input a la derecha
    }
  }

/-- La máquina acepta si alcanza el estado de aceptación -/
def accepts (input : List Σ) : Prop :=
  ∃ t : ℕ, ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    c.state = StateSet.accept

/-- La máquina rechaza si alcanza el estado de rechazo -/
def rejects (input : List Σ) : Prop :=
  ∃ t : ℕ, ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    c.state = StateSet.reject

/-- La máquina se detiene en tiempo t -/
def haltsIn (input : List Σ) (t : ℕ) : Prop :=
  ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    (c.state = StateSet.accept ∨ c.state = StateSet.reject) ∧
    M.step c = none

/-- La máquina se detiene eventualmente -/
def halts (input : List Σ) : Prop :=
  ∃ t : ℕ, M.haltsIn input t

/-- Tiempo de ejecución (devuelve el mínimo t donde se detiene) -/
noncomputable def runTime (input : List Σ) : ℕ :=
  if h : M.halts input then
    Nat.find h
  else
    0  -- Por definición, si no para, tiempo = 0

end TuringMachine
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

/-- Un lenguaje es un conjunto de strings -/
def Language (Σ : Type*) := List Σ → Prop

/-- Una máquina decide un lenguaje -/
def Decides {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (L : Language Σ) : Prop :=
  ∀ w : List Σ, 
    (L w ↔ M.accepts w) ∧ 
    (¬L w ↔ M.rejects w) ∧
    M.halts w

/-- Una máquina decide un lenguaje en tiempo f(n) -/
def DecidesInTime {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (L : Language Σ) (f : ℕ → ℕ) : Prop :=
  Decides M L ∧
  ∀ w : List Σ, M.runTime w ≤ f w.length

-- ══════════════════════════════════════════════════════════════
-- PROPIEDADES BÁSICAS
-- ══════════════════════════════════════════════════════════════

theorem halt_or_loop {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.halts w ∨ ¬M.halts w := by
  exact Classical.em _

theorem accepts_implies_halts {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.accepts w → M.halts w := by
  intro ⟨t, c, h_run, h_accept⟩
  use t, c
  exact ⟨h_run, Or.inl h_accept, by
    have := M.halt_no_transition c.tape.current
    rw [h_accept] at this
    exact this.1⟩

theorem rejects_implies_halts {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.rejects w → M.halts w := by
  intro ⟨t, c, h_run, h_reject⟩
  use t, c
  exact ⟨h_run, Or.inr h_reject, by
    have := M.halt_no_transition c.tape.current
    rw [h_reject] at this
    exact this.2⟩

theorem decides_implies_total {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (L : Language Σ) :
  Decides M L → ∀ w : List Σ, M.halts w := by
  intro h_decides w
  exact (h_decides w).2.2
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
