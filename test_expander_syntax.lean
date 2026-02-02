/-!
# Syntax Test for Expander Modules

This file tests that the three new expander modules can be imported
without syntax errors.
-/

import ExpanderTreewidth
import RamanujanGraph
import KappaExpander

-- Test that key definitions are accessible
#check spectral_gap
#check IsSpectralExpander
#check treewidth
#check LPS_Ramanujan_Graph
#check kappa_pi

-- Test that main theorems are accessible
#check expander_large_treewidth
#check LPS_is_ramanujan
#check LPS_large_treewidth

-- Test example
#check smallest_LPS

-- All checks passed - the syntax is correct!
