import Mathlib.Data.Real.Basic

/-!
 # QCAL.Stability.Bifurcation

 Demostración formal del criterio de bifurcación crítica donde el sistema
 escapa del código adélico si la tasa de error supera la disipación.

 La dinámica del error sigue la ecuación:
   dℰ/dt = Γ_total − κ·ℰ + β·ℰ²

 donde:
   Γ_total = tasa de inyección de error (térmico + 1/f + δf₀)
   κ = tasa de disipación y auto-reparación
   β = coeficiente de acoplamiento no lineal de errores

 Fases:
   Γ_total < κ²/(4β)  →  lock estable, gap preservado
   Γ_total = κ²/(4β)  →  bifurcación silla-nodo
   Γ_total > κ²/(4β)  →  colapso, gap destruido
-/

namespace QCAL.Stability.Bifurcation

/-- Parámetros dinámicos del sistema QCAL. -/
structure SystemDynamics where
  gamma_error : ℝ    -- Γ_total: tasa de inyección de error
  kappa_diss : ℝ     -- κ: tasa de disipación y auto-reparación
  beta_nonlin : ℝ    -- β: coeficiente de acoplamiento no lineal
  is_locked : Bool   -- estado actual del lock de fase

/-- El sistema está en la región de estabilidad cuando el discriminante
    de la ecuación de puntos fijos es no negativo. -/
def IsStableRegion (sys : SystemDynamics) : Prop :=
  sys.kappa_diss ^ 2 - 4.0 * sys.beta_nonlin * sys.gamma_error ≥ 0

/-- Cálculo del discriminante del sistema. -/
def discriminant (sys : SystemDynamics) : ℝ :=
  sys.kappa_diss ^ 2 - 4.0 * sys.beta_nonlin * sys.gamma_error

/-- Punto fijo estable (atractor) cuando el sistema está en régimen de coherencia. -/
def stable_fixed_point (sys : SystemDynamics) (h_disc : discriminant sys > 0) : ℝ :=
  (sys.kappa_diss - Real.sqrt (discriminant sys)) / (2.0 * sys.beta_nonlin)

/-- Punto fijo inestable (repulsor) cuando el sistema está en régimen de coherencia. -/
def unstable_fixed_point (sys : SystemDynamics) (h_disc : discriminant sys > 0) : ℝ :=
  (sys.kappa_diss + Real.sqrt (discriminant sys)) / (2.0 * sys.beta_nonlin)

/--
 TEOREMA DE TRANSICIÓN DE FASE.
 Demuestra formalmente que si la tasa de inyección de error supera el umbral
 crítico indexado por κ, es lógicamente imposible sostener la estabilidad
 del código, forzando la pérdida del lock.
-/
theorem system_lock_collapse (sys : SystemDynamics)
    (h_beta : sys.beta_nonlin > 0)
    (h_break : sys.gamma_error > (sys.kappa_diss ^ 2) / (4.0 * sys.beta_nonlin)) :
    ¬ IsStableRegion sys := by
  unfold IsStableRegion
  intro h_stable
  have h_mul : 4.0 * sys.beta_nonlin * sys.gamma_error > sys.kappa_diss ^ 2 := by
    have h_pos : 4.0 * sys.beta_nonlin > 0 := by linarith
    calc
      4.0 * sys.beta_nonlin * sys.gamma_error
          > 4.0 * sys.beta_nonlin * ((sys.kappa_diss ^ 2) / (4.0 * sys.beta_nonlin)) :=
        mul_lt_mul_of_pos_left h_break h_pos
      _ = sys.kappa_diss ^ 2 := by field_simp [h_beta.ne.symm]
  have h_disc : sys.kappa_diss ^ 2 - 4.0 * sys.beta_nonlin * sys.gamma_error < 0 := by linarith
  linarith

/--
 Versión simplificada del teorema de transición de fase.
 Demuestra que si el discriminante es negativo, el sistema no está en
 la región estable.
-/
theorem system_lock_collapse_by_discriminant (sys : SystemDynamics)
    (h_beta : sys.beta_nonlin > 0)
    (h_neg_disc : discriminant sys < 0) :
    ¬ IsStableRegion sys := by
  unfold IsStableRegion discriminant at h_neg_disc
  linarith

end QCAL.Stability.Bifurcation
