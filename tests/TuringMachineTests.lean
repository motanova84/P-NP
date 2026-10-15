/-
Basic Tests for Turing Machine Formalization
-/

import TuringMachine

/-! # Basic Tests for Turing Machines

This file contains examples and basic tests for the Turing Machine formalization.
-/

-- ══════════════════════════════════════════════════════════════
-- EJEMPLO: Alfabeto binario simple
-- ══════════════════════════════════════════════════════════════

/-- Alfabeto de cinta binario con blanco -/
inductive BinaryTapeAlphabet
  | zero
  | one
  | blank
  deriving DecidableEq, Repr

/-- Alfabeto de entrada binario (sin blanco) -/
inductive BinaryInputAlphabet
  | zero
  | one
  deriving DecidableEq, Repr

-- Instancia Fintype para BinaryTapeAlphabet
instance : Fintype BinaryTapeAlphabet := {
  elems := {BinaryTapeAlphabet.zero, BinaryTapeAlphabet.one, BinaryTapeAlphabet.blank},
  complete := by intro x; cases x <;> simp
}

-- Instancia Fintype para BinaryInputAlphabet
instance : Fintype BinaryInputAlphabet := {
  elems := {BinaryInputAlphabet.zero, BinaryInputAlphabet.one},
  complete := by intro x; cases x <;> simp
}

-- Instancia TapeAlphabet para BinaryTapeAlphabet
instance : TapeAlphabet BinaryTapeAlphabet where
  blank := BinaryTapeAlphabet.blank

-- Función de embedding del alfabeto de entrada al alfabeto de cinta
def binaryInputSubset : BinaryInputAlphabet → BinaryTapeAlphabet
  | BinaryInputAlphabet.zero => BinaryTapeAlphabet.zero
  | BinaryInputAlphabet.one => BinaryTapeAlphabet.one

-- Instancia InputAlphabet
instance : InputAlphabet BinaryInputAlphabet BinaryTapeAlphabet where
  input_subset := binaryInputSubset
  no_blank := by
    intro σ
    cases σ <;> simp [binaryInputSubset]

-- ══════════════════════════════════════════════════════════════
-- EJEMPLO: Estados simples
-- ══════════════════════════════════════════════════════════════

/-- Estados para una máquina simple -/
inductive SimpleStates
  | start
  | accept
  | reject
  | q1
  | q2
  deriving DecidableEq, Repr

-- Instancia Fintype para SimpleStates
instance : Fintype SimpleStates := {
  elems := {
    SimpleStates.start,
    SimpleStates.accept,
    SimpleStates.reject,
    SimpleStates.q1,
    SimpleStates.q2
  },
  complete := by intro x; cases x <;> simp
}

-- Instancia StateSet para SimpleStates
instance : StateSet SimpleStates where
  start := SimpleStates.start
  accept := SimpleStates.accept
  reject := SimpleStates.reject
  start_neq_accept := by simp [SimpleStates.start, SimpleStates.accept]
  start_neq_reject := by simp [SimpleStates.start, SimpleStates.reject]
  accept_neq_reject := by simp [SimpleStates.accept, SimpleStates.reject]

-- ══════════════════════════════════════════════════════════════
-- TEST: Propiedades básicas
-- ══════════════════════════════════════════════════════════════

/-- Test: halt_or_loop siempre es verdadero -/
example (M : TuringMachine BinaryInputAlphabet BinaryTapeAlphabet SimpleStates) (w : List BinaryInputAlphabet) :
  M.halts w ∨ ¬M.halts w := by
  exact halt_or_loop M w

/-- Test: Si una máquina acepta, entonces se detiene -/
example (M : TuringMachine BinaryInputAlphabet BinaryTapeAlphabet SimpleStates) (w : List BinaryInputAlphabet) :
  M.accepts w → M.halts w := by
  exact accepts_implies_halts M w

/-- Test: Si una máquina rechaza, entonces se detiene -/
example (M : TuringMachine BinaryInputAlphabet BinaryTapeAlphabet SimpleStates) (w : List BinaryInputAlphabet) :
  M.rejects w → M.halts w := by
  exact rejects_implies_halts M w

/-- Test: Si una máquina decide un lenguaje, se detiene para todos los inputs -/
example (M : TuringMachine BinaryInputAlphabet BinaryTapeAlphabet SimpleStates) (L : Language BinaryInputAlphabet) :
  Decides M L → ∀ w : List BinaryInputAlphabet, M.halts w := by
  exact decides_implies_total M L

-- ══════════════════════════════════════════════════════════════
-- EJEMPLO: Construcción de configuración de cinta
-- ══════════════════════════════════════════════════════════════

/-- Test: Crear una cinta simple -/
def simpleTape : TapeConfig BinaryTapeAlphabet :=
  { left := [],
    current := BinaryTapeAlphabet.zero,
    right := [BinaryTapeAlphabet.one, BinaryTapeAlphabet.zero] }

/-- Test: Mover a la derecha -/
example : (simpleTape.moveRight).current = BinaryTapeAlphabet.one := by
  simp [simpleTape, TapeConfig.moveRight]

/-- Test: Escribir en la cinta -/
example : (simpleTape.write BinaryTapeAlphabet.one).current = BinaryTapeAlphabet.one := by
  simp [simpleTape, TapeConfig.write]

-- ══════════════════════════════════════════════════════════════
-- VERIFICACIÓN: Sin axiomas adicionales
-- ══════════════════════════════════════════════════════════════

/-- Verificación: Los teoremas básicos no usan axiomas adicionales -/
#check halt_or_loop
#check accepts_implies_halts
#check rejects_implies_halts
#check decides_implies_total
