/-!
# Polynomial-Time Reductions and Complexity Classes

This module formalizes:
* Languages and decision problems
* Turing machines and computation models
* Time complexity classes (NTIME, P, NP)
* Polynomial-time reductions
* NP-completeness

## Main Definitions

* `Language`: A set of strings (decision problem)
* `TuringMachine`: Abstract Turing machine model
* `NTIME`: Non-deterministic time complexity class
* `NP_Class`: The class NP (languages verifiable in polynomial time)
* `PolynomialReduction`: Polynomial-time many-one reduction
* `NPComplete`: NP-complete problems

-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

namespace Formal.Reductions

-- ══════════════════════════════════════════════════════════════
-- BASICS: ALPHABETS AND LANGUAGES
-- ══════════════════════════════════════════════════════════════

/-- A language over alphabet Σ is a set of strings -/
def Language (Σ : Type*) := List Σ → Prop

/-- Input alphabet for Turing machines -/
class InputAlphabet (Σ Γ : Type*) where
  /-- Every input symbol is also a tape symbol -/
  embed : Σ → Γ
  /-- Blank symbol -/
  blank : Γ
  /-- Blank is not in input alphabet -/
  blank_not_input : ∀ σ : Σ, embed σ ≠ blank

/-- State set for Turing machines -/
class StateSet (Q : Type*) where
  /-- Initial state -/
  q_start : Q
  /-- Accept state -/
  q_accept : Q
  /-- Reject state -/
  q_reject : Q
  /-- Accept and reject are different -/
  accept_neq_reject : q_accept ≠ q_reject

-- ══════════════════════════════════════════════════════════════
-- TURING MACHINES
-- ══════════════════════════════════════════════════════════════

/-- Direction of tape head movement -/
inductive Direction
  | left
  | right
  | stay
deriving Repr, DecidableEq

/-- Configuration of a Turing machine at a point in time -/
structure Configuration (Σ Γ Q : Type*) [InputAlphabet Σ Γ] where
  /-- Current state -/
  state : Q
  /-- Position of tape head -/
  head_pos : ℤ
  /-- Tape contents (function from position to symbol) -/
  tape : ℤ → Γ

/-- Abstract Turing machine -/
structure TuringMachine (Σ Γ Q : Type*) [InputAlphabet Σ Γ] [StateSet Q] where
  /-- Transition function: (state, symbol) → (new_state, new_symbol, direction) -/
  δ : Q → Γ → Option (Q × Γ × Direction)

/-- Initial configuration for input w -/
def initial_config {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q] 
  (w : List Σ) : Configuration Σ Γ Q :=
  { state := StateSet.q_start
    head_pos := 0
    tape := fun i =>
      if h : i.toNat < w.length ∧ i ≥ 0 then
        InputAlphabet.embed (w.get ⟨i.toNat, h.1⟩)
      else
        InputAlphabet.blank }

/-- One step of computation -/
def step {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q] 
  (M : TuringMachine Σ Γ Q) (c : Configuration Σ Γ Q) : Option (Configuration Σ Γ Q) :=
  match M.δ c.state (c.tape c.head_pos) with
  | none => none  -- Machine halts
  | some (q', γ', dir) =>
    let new_pos := match dir with
      | Direction.left => c.head_pos - 1
      | Direction.right => c.head_pos + 1
      | Direction.stay => c.head_pos
    some { state := q'
           head_pos := new_pos
           tape := fun i => if i = c.head_pos then γ' else c.tape i }

/-- Multi-step computation -/
def steps {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) : ℕ → Configuration Σ Γ Q → Option (Configuration Σ Γ Q)
  | 0, c => some c
  | n + 1, c =>
    match steps M n c with
    | none => none
    | some c' => step M c'

/-- Machine accepts input w in exactly t steps -/
def acceptsInTime {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (w : List Σ) (t : ℕ) : Prop :=
  ∃ c : Configuration Σ Γ Q,
    steps M t (initial_config w) = some c ∧ c.state = StateSet.q_accept

/-- Machine accepts input w in at most t steps -/
def acceptsInTimeLE {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) (w : List Σ) (t : ℕ) : Prop :=
  ∃ t' ≤ t, acceptsInTime M w t'

/-- Language recognized by machine M -/
def recognizes {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q]
  (M : TuringMachine Σ Γ Q) : Language Σ :=
  fun w => ∃ t, acceptsInTime M w t

-- ══════════════════════════════════════════════════════════════
-- TIME COMPLEXITY CLASSES
-- ══════════════════════════════════════════════════════════════

/-- Non-deterministic time class NTIME(f) -/
def NTIME (f : ℕ → ℕ) : Type := 
  { L : Type // ∃ (Σ Γ Q : Type) (inst_ia : InputAlphabet Σ Γ) (inst_ss : StateSet Q),
    ∃ (lang : Language Σ) (M : @TuringMachine Σ Γ Q inst_ia inst_ss),
      (∀ w, lang w ↔ ∃ t ≤ f w.length, @acceptsInTime Σ Γ Q inst_ia inst_ss M w t) }

/-- The class NP = ⋃ₖ NTIME(nᵏ) -/
def NP_Class : Type :=
  { L : Type // ∃ k : ℕ, L ∈ NTIME (fun n => n ^ k) }

/-- Membership in NP_Class as a predicate -/
def in_NP_Class {Σ : Type*} (L : Language Σ) : Prop :=
  ∃ k : ℕ, ∃ (Γ Q : Type) (inst_ia : InputAlphabet Σ Γ) (inst_ss : StateSet Q),
    ∃ (M : @TuringMachine Σ Γ Q inst_ia inst_ss),
      (∀ w, L w ↔ ∃ t ≤ w.length ^ k, @acceptsInTime Σ Γ Q inst_ia inst_ss M w t)

notation L " ∈ " NP_Class => in_NP_Class L

-- ══════════════════════════════════════════════════════════════
-- POLYNOMIAL-TIME REDUCTIONS
-- ══════════════════════════════════════════════════════════════

/-- A function is polynomial-time computable -/
structure PolynomialTimeComputable {Σ₁ Σ₂ : Type*} (f : List Σ₁ → List Σ₂) where
  /-- Output length is polynomially bounded -/
  poly_bounded : ∃ k : ℕ, ∀ w, (f w).length ≤ w.length ^ k
  /-- Function is computable in polynomial time -/
  poly_time : ∃ k : ℕ, ∃ (Γ Q : Type) (inst_ia : InputAlphabet Σ₁ Γ) (inst_ss : StateSet Q),
    ∃ (M : @TuringMachine Σ₁ Γ Q inst_ia inst_ss),
      ∀ w, ∃ t ≤ w.length ^ k, @acceptsInTime Σ₁ Γ Q inst_ia inst_ss M w t

/-- Polynomial-time many-one reduction from L₁ to L₂ -/
structure PolynomialReduction {Σ₁ Σ₂ : Type*} (L₁ : Language Σ₁) (L₂ : Language Σ₂) where
  /-- The reduction function -/
  f : List Σ₁ → List Σ₂
  /-- Function is polynomial-time computable -/
  computable : PolynomialTimeComputable f
  /-- Function preserves language membership -/
  preserves : ∀ w, L₁ w ↔ L₂ (f w)

notation:50 L₁ " ≤ₚ " L₂ => PolynomialReduction L₁ L₂

-- ══════════════════════════════════════════════════════════════
-- NP-COMPLETENESS
-- ══════════════════════════════════════════════════════════════

/-- A language L is NP-complete if:
    1. L ∈ NP
    2. Every language in NP reduces to L -/
structure NPComplete {Σ : Type*} (L : Language Σ) where
  /-- L is in NP -/
  in_np : L ∈ NP_Class
  /-- Every language in NP reduces to L -/
  np_hard : ∀ {Σ' : Type*} (L' : Language Σ'), L' ∈ NP_Class → L' ≤ₚ L

-- ══════════════════════════════════════════════════════════════
-- BASIC LEMMAS
-- ══════════════════════════════════════════════════════════════

/-- Polynomial-time reductions are transitive -/
theorem reduction_transitive {Σ₁ Σ₂ Σ₃ : Type*}
  {L₁ : Language Σ₁} {L₂ : Language Σ₂} {L₃ : Language Σ₃}
  (r₁₂ : L₁ ≤ₚ L₂) (r₂₃ : L₂ ≤ₚ L₃) : L₁ ≤ₚ L₃ := by
  -- Compose the reduction functions
  use { f := fun w => r₂₃.f (r₁₂.f w)
        computable := by
          constructor
          · -- Output length bound
            obtain ⟨k₁, h₁⟩ := r₁₂.computable.poly_bounded
            obtain ⟨k₂, h₂⟩ := r₂₃.computable.poly_bounded
            use k₁ * k₂
            intro w
            calc (r₂₃.f (r₁₂.f w)).length
              _ ≤ (r₁₂.f w).length ^ k₂        := h₂ (r₁₂.f w)
              _ ≤ (w.length ^ k₁) ^ k₂         := by
                apply Nat.pow_le_pow_left
                exact h₁ w
              _ = w.length ^ (k₁ * k₂)         := by ring_nf
          · -- Polynomial time
            sorry  -- Requires composition of TM computations
        preserves := fun w => by
          -- Preserves language membership via composition
          calc L₁ w
            _ ↔ L₂ (r₁₂.f w)                := r₁₂.preserves w
            _ ↔ L₃ (r₂₃.f (r₁₂.f w))       := r₂₃.preserves (r₁₂.f w) }

/-- Class P (placeholder for formal P definition) -/
axiom P_Class : Type

/-- Membership in P_Class -/
axiom in_P_Class {Σ : Type*} (L : Language Σ) : Prop

/-- If L is NP-complete and L ∈ P, then P = NP -/
theorem np_complete_in_p_implies_p_eq_np {Σ : Type*} (L : Language Σ)
  (h_complete : NPComplete L) (h_in_p : in_P_Class L) :
  ∀ {Σ' : Type*} (L' : Language Σ'), in_NP_Class L' → in_P_Class L' := by
  intro Σ' L' h_L'_in_np
  -- L' ∈ NP and L is NP-complete, so L' ≤ₚ L
  have r := h_complete.np_hard L' h_L'_in_np
  -- L ∈ P and L' ≤ₚ L implies L' ∈ P
  sorry  -- Requires formalization that reductions preserve membership in P

end Formal.Reductions
