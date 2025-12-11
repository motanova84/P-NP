-- Reductions.lean
-- Reducciones polinomiales y NP-completitud

import ComplexityClasses
import Mathlib.Data.List.Basic

/-! # Reducciones Polinomiales

Definiciones de reducibilidad y NP-completitud.

-/

-- ══════════════════════════════════════════════════════════════
-- REDUCCIONES EN TIEMPO POLINOMIAL
-- ══════════════════════════════════════════════════════════════

/-- Función computable por una Máquina de Turing -/
structure ComputableFunction (Σ₁ Σ₂ : Type*) where
  f : List Σ₁ → List Σ₂
  /-- Existe TM que computa f -/
  computable : ∃ (Γ Q : Type*) [InputAlphabet Σ₁ Γ] [StateSet Q],
    ∃ (M : TuringMachine Σ₁ Γ Q),
    ∀ w : List Σ₁, ∃ t : ℕ,
      ∃ c : Config Σ₁ Γ Q,
      M.run (M.initialConfig w) t = some c ∧
      c.state = StateSet.accept ∧
      tape_output c = f w  -- Salida codificada en cinta

/-- Reducción en tiempo polinomial -/
def PolyTimeReducible {Σ₁ Σ₂ : Type*} 
  (L₁ : Language Σ₁) (L₂ : Language Σ₂) : Prop :=
  ∃ (f : ComputableFunction Σ₁ Σ₂),
  ∃ (k : ℕ),
  (∀ w : List Σ₁, f.f w |>.length ≤ w.length ^ k) ∧  -- Poly-bounded
  (∃ (Γ Q : Type*) [InputAlphabet Σ₁ Γ] [StateSet Q],  -- Poly-time
   ∃ (M : TuringMachine Σ₁ Γ Q),
   ∀ w : List Σ₁, M.runTime w ≤ w.length ^ k) ∧
  (∀ w : List Σ₁, L₁ w ↔ L₂ (f.f w))  -- Preserva pertenencia

notation:50 L₁ " ≤ₚ " L₂ => PolyTimeReducible L₁ L₂

-- ══════════════════════════════════════════════════════════════
-- NP-HARDNESS Y NP-COMPLETITUD
-- ══════════════════════════════════════════════════════════════

/-- L es NP-hard si todo lenguaje en NP se reduce a L -/
def NPHard {Σ : Type*} (L : Language Σ) : Prop :=
  ∀ (Σ' : Type*) (L' : Language Σ'), (Σ', L') ∈ NP_Class → L' ≤ₚ L

/-- L es NP-complete si está en NP y es NP-hard -/
def NPComplete {Σ : Type*} (L : Language Σ) : Prop :=
  (Σ, L) ∈ NP_Class ∧ NPHard L

-- ══════════════════════════════════════════════════════════════
-- PROPIEDADES DE REDUCCIONES
-- ══════════════════════════════════════════════════════════════

/-- Reducibilidad es transitiva -/
theorem poly_reduce_trans {Σ₁ Σ₂ Σ₃ : Type*}
  (L₁ : Language Σ₁) (L₂ : Language Σ₂) (L₃ : Language Σ₃) :
  L₁ ≤ₚ L₂ → L₂ ≤ₚ L₃ → L₁ ≤ₚ L₃ := by
  intro ⟨f, k₁, hf_bound, hf_time, hf_preserve⟩ ⟨g, k₂, hg_bound, hg_time, hg_preserve⟩
  -- Composición f ∘ g es poly-time computable
  
  -- Construir la función composición
  let h : ComputableFunction Σ₁ Σ₃ := {
    f := fun w => g.f (f.f w),
    computable := by
      -- La composición de funciones computables es computable
      sorry
  }
  
  use h
  
  -- Elegir k = k₁ * k₂ como exponente polinomial
  use k₁ * k₂
  
  constructor
  · -- La salida tiene tamaño polinomial
    intro w
    calc (g.f (f.f w)).length
        ≤ (f.f w).length ^ k₂ := hg_bound (f.f w)
      _ ≤ (w.length ^ k₁) ^ k₂ := by
          apply Nat.pow_le_pow_right
          · omega
          · exact hf_bound w
      _ = w.length ^ (k₁ * k₂) := by ring_nf
  
  constructor
  · -- El cálculo toma tiempo polinomial
    sorry  -- Composición de máquinas poly-time es poly-time
  
  · -- Preserva pertenencia al lenguaje
    intro w
    calc L₁ w
        ↔ L₂ (f.f w) := hf_preserve w
      _ ↔ L₃ (g.f (f.f w)) := hg_preserve (f.f w)

/-- Si L es NP-complete y L ≤ₚ L', entonces L' es NP-hard -/
theorem np_complete_reduces {Σ Σ' : Type*}
  (L : Language Σ) (L' : Language Σ') :
  NPComplete L → L ≤ₚ L' → NPHard L' := by
  intro ⟨h_inNP, h_hard⟩ h_reduce
  intro Σ'' L'' h_L''_inNP
  -- L'' ≤ₚ L (por NP-hardness de L)
  -- L ≤ₚ L' (por hipótesis)
  -- Por transitividad: L'' ≤ₚ L'
  have h1 := h_hard Σ'' L'' h_L''_inNP
  exact poly_reduce_trans L'' L L' h1 h_reduce

/-- Si algún NP-complete está en P, entonces P = NP -/
theorem np_complete_in_P_implies_P_eq_NP {Σ : Type*}
  (L : Language Σ) :
  NPComplete L → (Σ, L) ∈ P_Class → P_Class = NP_Class := by
  intro ⟨h_inNP, h_hard⟩ h_inP
  ext ⟨Σ', L'⟩
  constructor
  · -- P ⊆ NP (ya probado)
    exact fun h => P_subset_NP h
  · -- NP ⊆ P
    intro h_L'_inNP
    -- L' ≤ₚ L (por NP-hardness)
    have h_reduce : L' ≤ₚ L := h_hard Σ' L' h_L'_inNP
    
    -- Obtener la reducción
    obtain ⟨f, k, hf_bound, ⟨Γ_f, Q_f, inst1, inst2, M_f, hf_time⟩, hf_preserve⟩ := h_reduce
    
    -- L ∈ P, así que existe una MT que lo decide en tiempo polinomial
    obtain ⟨Γ_L, Q_L, inst3, inst4, M_L, k_L, hL_time, hL_decide⟩ := h_inP
    
    -- Construir MT para L' que primero reduce con f, luego usa M_L
    use Γ_L, Q_L
    
    -- Componer las máquinas
    sorry  -- La composición M_L ∘ M_f decide L' en tiempo polinomial
