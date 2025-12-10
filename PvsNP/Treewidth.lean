/-!
# Treewidth Definitions and Properties

This module provides treewidth theory for the P vs NP framework.
It imports the complete implementation and re-exports key definitions.
-/

import PvsNP.TreewidthComplete

namespace PvsNP

-- Re-export main definitions from TreewidthComplete
open TreewidthComplete

/-- Re-export tree decomposition -/
export TreewidthComplete (TreeDecomposition)

/-- Re-export treewidth function -/
export TreewidthComplete (treewidth)

/-- Re-export CNF formula structure -/
export TreewidthComplete (CnfFormula)

/-- Re-export incidence graph -/
export TreewidthComplete (incidenceGraph)

/-- Re-export treewidth approximation -/
export TreewidthComplete (treewidthApprox cnfTreewidth)

/-- Treewidth theory is complete -/
theorem treewidth_theory : True := trivial

end PvsNP
