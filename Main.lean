import PNP.Basic
import PNP.Lemma635
import PNP.SupportingLemmas
import PNP.Theorem631

def main : IO Unit := do
  IO.println "P-NP Proof Framework"
  IO.println "====================="
  IO.println ""
  IO.println "This project formalizes the proof structure for P≠NP"
  IO.println "based on information complexity lower bounds and lifting theorems."
  IO.println ""
  IO.println "Key components:"
  IO.println "- Lemma 6.35: Structural Reduction Preserving IC"
  IO.println "- Lemma 6.32: RAM to Protocol Simulation"
  IO.println "- Lemma 6.33: Anti-Bypass"
  IO.println "- Theorem 6.34: Computational Dichotomy"
  IO.println "- Theorem 6.31: Main Lifting Theorem"
