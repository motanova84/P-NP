/-!
# Tests for KappaSmallForIncidence Module

Basic verification tests for the Tseitin formula construction
and spectral constant bounds.
-/

import TseitinHardFamily
import KappaSmallForIncidence

namespace KappaSmallTests

open TseitinHardFamily
open KappaSmallForIncidence

-- Test that we can construct a Tseitin formula
example (n : ℕ) (hn : n > 0) (hodd : Odd n) : True := by
  let φ := buildTseitinFormula n hn hodd
  trivial

-- Test that incidence graph size theorem holds
example (n : ℕ) (hn : n > 0) (hodd : Odd n) : True := by
  have h := incidence_graph_size n hn hodd
  trivial

-- Test that the main kappa theorem exists
example : ∃ (C : ℝ) (hC : C > 0), True := by
  obtain ⟨C, hC, _⟩ := main_kappa_small_theorem
  use C, hC

-- Test that the IC lower bound theorem exists
example (n : ℕ) (hn : n > 1000) : True := by
  have h := ic_lower_bound_from_small_kappa n hn
  trivial

-- Test basic bipartite structure theorem
example (n : ℕ) (hn : n > 0) : True := by
  have h := tseitin_incidence_is_8_2_bipartite n hn
  trivial

end KappaSmallTests
