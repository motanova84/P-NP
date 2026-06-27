/-
╔══════════════════════════════════════════════════════════════════╗
║  AXIOMA 2 — NO-HAUSDORFF PLANCKIANO                           ║
║  A escala de Planck, el espacio-tiempo es un grafo no-Hausdorff║
║  27/Jun/2026 · f₀ = 141.7001 Hz                               ║
╚══════════════════════════════════════════════════════════════════╝
-/
import QCal.EspacioTiempo.Coherente
import Mathlib.Topology.Basic

axiom NoHausdorffPlanckiano : ∀ (α : Type u) [Fintype α] (G : SimpleGraph α),
  ∃ (v w : α), v ≠ w ∧
  ¬∃ (U V : Set α), IsOpen U ∧ IsOpen V ∧ v ∈ U ∧ w ∈ V ∧ U ∩ V = ∅
