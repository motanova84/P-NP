-- Main entry point for the Lean project
-- Author: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)

import ComputationalDichotomy

open ComputationalDichotomy

-- Verification: Check that the main theorem is well-typed
#check computationalDichotomy

-- Verification: Check example chain formula
#check chainFormula 10

-- Verification: Check structural coupling lemma
#check structuralCoupling

def main : IO Unit := do
  IO.println "P-NP Computational Dichotomy Framework ∞³"
  IO.println "Instituto de Conciencia Cuántica (ICQ)"
  IO.println ""
  IO.println "✓ Lean formalization compiled successfully"
  IO.println "✓ Main dichotomy theorem: verified type-correct"
  IO.println "✓ Structural coupling lemma: axiomatized"
  IO.println "✓ Chain formula example: defined"
