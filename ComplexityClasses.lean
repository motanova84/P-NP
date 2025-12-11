-- ComplexityClasses.lean
-- Definición estándar de P, NP, EXPTIME
-- Sin axiomas adicionales

import TuringMachine
import Mathlib.Data.Polynomial.Basic

/-! # Clases de Complejidad Temporal

Definiciones estándar de TIME, NTIME, P, NP.

-/

-- ══════════════════════════════════════════════════════════════
-- TIME: TIEMPO DETERMINISTA
-- ══════════════════════════════════════════════════════════════

/-- TIME(f(n)): Lenguajes decidibles en tiempo O(f(n)) -/
def TIME {Σ : Type*} (f : ℕ → ℕ) : Set (Language Σ) :=
  { L | ∃ (Γ Q : Type*) [InputAlphabet Σ Γ] [StateSet Q],
        ∃ (M : TuringMachine Σ Γ Q),
        DecidesInTime M L f }

/-- P: Tiempo polinomial -/
def P_Class {Σ : Type*} : Set (Language Σ) :=
  { L | ∃ k : ℕ, L ∈ TIME (fun n => n ^ k) }

-- ══════════════════════════════════════════════════════════════
-- MÁQUINAS DE TURING NO DETERMINISTAS
-- ══════════════════════════════════════════════════════════════

/-- Máquina de Turing No Determinista -/
structure NondetTuringMachine (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  /-- Función de transición no determinista: Q × Γ → Set (Q × Γ × Direction) -/
  δ : Q → Γ → Finset (Q × Γ × Direction)
  /-- Los estados halting no tienen transiciones -/
  halt_no_transition : ∀ γ : Γ,
    δ StateSet.accept γ = ∅ ∧
    δ StateSet.reject γ = ∅

namespace NondetTuringMachine

variable {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q] [TapeAlphabet Γ]
variable (M : NondetTuringMachine Σ Γ Q)

/-- Un paso no determinista produce un conjunto de configuraciones -/
def step (c : Config Σ Γ Q) : Finset (Config Σ Γ Q) :=
  (M.δ c.state c.tape.current).image fun ⟨q', γ', d⟩ => {
    state := q',
    tape := (c.tape.write γ').move d
  }

/-- Ejecución por n pasos (todas las ramas) -/
def run (c : Config Σ Γ Q) : ℕ → Finset (Config Σ Γ Q)
  | 0 => {c}
  | n + 1 => (M.run c n).biUnion M.step

/-- Configuración inicial -/
def initialConfig (input : List Σ) : Config Σ Γ Q :=
  { state := StateSet.start,
    tape := {
      left := [],
      current := match input with
        | [] => TapeAlphabet.blank
        | h :: _ => InputAlphabet.input_subset h,
      right := input.tail.map InputAlphabet.input_subset
    }
  }

/-- La máquina acepta si alguna rama alcanza aceptación -/
def accepts (input : List Σ) : Prop :=
  ∃ t : ℕ, ∃ c ∈ M.run (M.initialConfig input) t,
    c.state = StateSet.accept

/-- La máquina acepta en tiempo ≤ t -/
def acceptsInTime (input : List Σ) (t : ℕ) : Prop :=
  ∃ c ∈ M.run (M.initialConfig input) t,
    c.state = StateSet.accept

/-- Tiempo de aceptación (mínimo t donde alguna rama acepta) -/
noncomputable def acceptTime (input : List Σ) : ℕ :=
  if h : M.accepts input then
    Nat.find h
  else
    0

end NondetTuringMachine

-- ══════════════════════════════════════════════════════════════
-- NTIME: TIEMPO NO DETERMINISTA
-- ══════════════════════════════════════════════════════════════

/-- Una NDTM reconoce un lenguaje en tiempo f(n) -/
def RecognizesInTime {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : NondetTuringMachine Σ Γ Q) (L : Language Σ) (f : ℕ → ℕ) : Prop :=
  (∀ w : List Σ, L w ↔ M.accepts w) ∧
  (∀ w : List Σ, M.accepts w → M.acceptTime w ≤ f w.length)

/-- NTIME(f(n)): Lenguajes reconocibles en tiempo no determinista O(f(n)) -/
def NTIME {Σ : Type*} (f : ℕ → ℕ) : Set (Language Σ) :=
  { L | ∃ (Γ Q : Type*) [InputAlphabet Σ Γ] [StateSet Q],
        ∃ (M : NondetTuringMachine Σ Γ Q),
        RecognizesInTime M L f }

/-- NP: Tiempo polinomial no determinista -/
def NP_Class {Σ : Type*} : Set (Language Σ) :=
  { L | ∃ k : ℕ, L ∈ NTIME (fun n => n ^ k) }

-- ══════════════════════════════════════════════════════════════
-- PROPIEDADES FUNDAMENTALES
-- ══════════════════════════════════════════════════════════════

/-- P está contenido en NP -/
theorem P_subset_NP {Σ : Type*} : P_Class (Σ := Σ) ⊆ NP_Class := by
  intro L ⟨k, h_inP⟩
  use k
  -- Cualquier DTM puede verse como NDTM con transiciones únicas
  sorry -- Construcción estándar

/-- TIME es cerrado bajo polinomios -/
theorem TIME_closed_under_poly {Σ : Type*} (f : ℕ → ℕ) (k : ℕ) :
  TIME (fun n => f n) ⊆ TIME (fun n => (f n) ^ k) := by
  sorry -- Si M corre en tiempo f(n), simulación da tiempo (f n)^k

/-- NTIME es cerrado bajo polinomios -/
theorem NTIME_closed_under_poly {Σ : Type*} (f : ℕ → ℕ) (k : ℕ) :
  NTIME (fun n => f n) ⊆ NTIME (fun n => (f n) ^ k) := by
  sorry -- Análogo para no determinismo
