/-
  P–NP Computational Dichotomy Framework ∞³
  Author: José Manuel Mota Burruezo (ICQ, 2025)
  Description:
    Main entry point for the Lean 4 formalization of
    the Treewidth–Information Complexity framework
    proving the structural separation P ≠ NP.
-/

import ComputationalDichotomy

def main : IO Unit := do
  IO.println "==============================================="
  IO.println "  P–NP Computational Dichotomy Framework ∞³"
  IO.println "==============================================="
  IO.println " Formal Lean verification using treewidth,"
  IO.println " separator information lower bounds (SILB),"
  IO.println " and internal information complexity."
  IO.println ""
  IO.println " → Powered by Lean 4 + Mathlib4"
  IO.println " → Author: José Manuel Mota Burruezo (ICQ)"
  IO.println " → Verification module: ComputationalDichotomy.lean"
