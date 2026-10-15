/-
Test file for ComplexityClasses.lean
Verifies that the basic definitions compile and type-check correctly.
-/

import ComplexityClasses

-- Test that we can reference the basic types
example : Type := Language Bool

-- Test that TIME is defined
example : Set (Language Bool) := TIME (fun n => n)

-- Test that P_Class is defined
example : Set (Language Bool) := P_Class

-- Test that NTIME is defined  
example : Set (Language Bool) := NTIME (fun n => n)

-- Test that NP_Class is defined
example : Set (Language Bool) := NP_Class

-- Test that P ⊆ NP
example : P_Class (Σ := Bool) ⊆ NP_Class := P_subset_NP

-- Test that theorems are available
example (f : ℕ → ℕ) (k : ℕ) : TIME (fun n => f n) ⊆ TIME (fun n => (f n) ^ k) := 
  TIME_closed_under_poly f k

example (f : ℕ → ℕ) (k : ℕ) : NTIME (fun n => f n) ⊆ NTIME (fun n => (f n) ^ k) := 
  NTIME_closed_under_poly f k

-- Test NondetTuringMachine structure is accessible
section NondetTest
  variable {Σ Γ Q : Type*} [InputAlphabet Σ Γ] [StateSet Q] [TapeAlphabet Γ]
  variable (M : NondetTuringMachine Σ Γ Q)
  
  -- Test that we can create and use NondetTuringMachine
  example (input : List Σ) : Config Σ Γ Q := M.initialConfig input
  
  example (input : List Σ) : Prop := M.accepts input
  
  example (input : List Σ) (t : ℕ) : Prop := M.acceptsInTime input t
end NondetTest
