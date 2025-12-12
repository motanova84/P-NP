-- Test file for PNeqNP.lean
-- Verifies that the main theorem and its components are accessible

import PNeqNP

/-! # PNeqNP Tests

This file contains basic tests to verify that PNeqNP.lean is properly structured.
-/

-- Verify the main theorem is accessible
#check P_neq_NP

-- Verify type definitions
#check IncidenceVertex
#check IncidenceVertex.var
#check IncidenceVertex.clause

-- Verify function definitions
#check incidenceGraph
#check numVarsFormula
#check formulaIC

-- Verify complexity class definitions
#check P_Class
#check NP_Class
#check SAT_Language

-- Verify Turing machine definitions
#check TuringMachine
#check InputAlphabet
#check StateSet
#check Decides

-- Verify axioms for hard formulas
#check tseitin_expander_formula
#check tseitin_high_treewidth
#check ic_from_treewidth_bound
#check time_lower_bound_from_IC

-- Verify the NP-completeness axiom
#check SAT_is_NP_complete
#check NP_Complete

-- Example: Create an incidence vertex
def example_var : IncidenceVertex := IncidenceVertex.var 5
def example_clause : IncidenceVertex := IncidenceVertex.clause 3

#check example_var
#check example_clause

-- The main theorem states that P ≠ NP
theorem P_and_NP_are_different : P_Class ≠ NP_Class := P_neq_NP
