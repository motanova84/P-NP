import Mathlib.Data.Real.Basic
import NOESIS.Oracle
import NOESIS.Phase3_Closure
import NOESIS.Step9_DecisionBarrier
import NOESIS.ClosureLimit
import NOESIS.OperationalPipeline

namespace NOESIS

open NOESIS

/-- Constantes operativas ancladas del módulo NOESIS. -/
def f0 : ℝ := NOESIS.Oracle.f0
def psiThreshold : ℝ := NOESIS.Oracle.psiThreshold
def barrier : ℝ := NOESIS.ClosureLimit.barrier

/--
Ancla mínima de formalización:
el pipeline operativo del repositorio es total para cualquier lectura real.
-/
theorem pipeline_total (ψ : ℝ) :
    NOESIS.Operational.decision_bit ψ = true ∨
    NOESIS.Operational.decision_bit ψ = false :=
  NOESIS.Operational.pipeline_operational_total ψ

/--
Ancla mínima de separabilidad de barrera (capa de decisión).
-/
theorem decision_separation :
    let ψ_sat_min : ℝ := 2 / 3 - 1 / 8
    let ψ_unsat : ℝ := 0
    let b : ℝ := 1 / 3
    let error_num : ℝ := 1 / 24
    (ψ_sat_min - error_num > b) ∧ (b > ψ_unsat + error_num) := by
  simpa using NOESIS.DecisionBarrier.decision_separation_gap

end NOESIS
