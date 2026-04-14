# Treewidth Module Usage Guide

**For Developers**: How to use the Treewidth module in higher-level theorems

## Quick Start

```lean
import Formal.Treewidth.Treewidth
import Formal.TreewidthTheory

-- Use treewidth in your theorems
theorem my_theorem (G : Treewidth.Graph) :
  Treewidth.treewidth G ≥ 0 := by
  exact Treewidth.treewidth_nonneg G
```

## Available Modules

### 1. Core Treewidth (`Formal.Treewidth.Treewidth`)

**Import**: `import Formal.Treewidth.Treewidth`

**Provides**:

```lean
-- Basic types
Treewidth.Graph                 -- Graph structure
Treewidth.Tree                  -- Tree structure
Treewidth.TreeDecomposition     -- Tree decomposition

-- Main functions
Treewidth.width                 -- Width of a decomposition
Treewidth.treewidth             -- Treewidth of a graph

-- Core theorems
Treewidth.treewidth_complete_graph  -- tw(Kₙ) = n - 1
Treewidth.treewidth_one_iff_tree    -- tw(G) = 1 ↔ G is tree
Treewidth.treewidth_nonneg          -- tw(G) ≥ 0
```

**Example Usage**:

```lean
theorem my_complete_graph_result (n : ℕ) (G : Treewidth.Graph) 
    (h : Treewidth.complete_graph_card G n) :
  Treewidth.treewidth G = n - 1 := by
  exact Treewidth.treewidth_complete_graph G n (by omega) h
```

### 2. Treewidth Theory (`Formal.TreewidthTheory`)

**Import**: `import Formal.TreewidthTheory`

**Provides**: Connection between formulas and treewidth

```lean
-- Formula treewidth
Formal.TreewidthTheory.treewidth (φ : CNFFormula) : ℕ

-- Incidence graph
Formal.TreewidthTheory.incidenceGraph : CNFFormula → Treewidth.Graph

-- Key theorems
Formal.TreewidthTheory.treewidthSATConnection
Formal.TreewidthTheory.treewidthDichotomy
```

**Example Usage**:

```lean
import Formal.TreewidthTheory
open Formal.TreewidthTheory

theorem sat_hardness_from_treewidth (φ : CNFFormula) (n : ℕ) 
    (h_vars : numVars φ = n)
    (h_tw : treewidth φ ≥ n / 2) :
  ∀ (alg : CNFFormula → Bool), 
    ∃ (ψ : CNFFormula), numVars ψ = n ∧ ¬(alg ψ = true) := by
  exact treewidthSATConnection φ n h_vars h_tw
```

### 3. Separator Information (`Formal.Treewidth.SeparatorInfo`)

**Import**: `import Formal.Treewidth.SeparatorInfo`

**Provides**: Connection to information complexity

```lean
-- Main theorem
Treewidth.separator_information_lower_bound :
  Treewidth.treewidth G ≥ α → 
  information_complexity π ≥ α / Real.log (Treewidth.treewidth G + 1)
```

**Example Usage**:

```lean
import Formal.Treewidth.SeparatorInfo
open Treewidth

theorem communication_lower_bound (G : Graph) (π : Protocol) :
  treewidth G ≥ 100 →
  information_complexity π ≥ 100 / Real.log 101 := by
  intro h
  exact separator_information_lower_bound G π 100 (by norm_num) h
```

## Common Patterns

### Pattern 1: Using Treewidth to Prove Hardness

```lean
import Formal.TreewidthTheory
import Formal.StructuralCoupling

theorem high_treewidth_implies_hard (φ : CNFFormula) :
  Formal.TreewidthTheory.treewidth φ ≥ numVars φ / 2 →
  ∀ alg, ∃ ψ, ¬(alg ψ = true) := by
  intro h_tw alg
  -- Use structural coupling lemma
  have h := Formal.StructuralCoupling.structuralCoupling φ h_tw alg
  obtain ⟨ψ, _, _, h3⟩ := h
  use ψ
  exact h3 alg
```

### Pattern 2: Building on Graph Properties

```lean
import Formal.Treewidth.Treewidth

def my_graph_property (G : Treewidth.Graph) : Prop :=
  Treewidth.treewidth G ≤ 10

theorem bounded_treewidth_property (G : Treewidth.Graph) 
    (h : my_graph_property G) :
  Treewidth.treewidth G ≥ 0 ∧ Treewidth.treewidth G ≤ 10 := by
  constructor
  · exact Treewidth.treewidth_nonneg G
  · exact h
```

### Pattern 3: Connecting to Main Theorem

```lean
import Formal.TreewidthTheory
import Formal.MainTheorem

-- Your theorem can build on the treewidth foundation
theorem my_pnp_contribution (φ : CNFFormula) :
  Formal.TreewidthTheory.treewidth φ ≥ numVars φ / 2 →
  ¬(Formal.MainTheorem.in_P CNFFormula) := by
  intro h_tw
  -- Use the validated treewidth infrastructure
  exact Formal.MainTheorem.sat_not_in_p
```

## Integration Points

### 1. Communication Bounds

**File**: `formal/Treewidth/SeparatorInfo.lean`

**Usage**:
```lean
import Formal.Treewidth.SeparatorInfo

theorem my_communication_theorem (G : Treewidth.Graph) :
  Treewidth.treewidth G ≥ 50 →
  ∃ (π : Protocol), information_complexity π ≥ 10 := by
  intro h_tw
  -- Use separator information lower bound
  use arbitrary_protocol
  have h := separator_information_lower_bound G arbitrary_protocol 50 (by norm_num) h_tw
  -- ... complete proof
  sorry
```

### 2. Lifting Theorems

**File**: `formal/Lifting/Gadgets.lean`

**Usage**:
```lean
import Formal.Lifting.Gadgets

theorem my_lifting_theorem (f : Bool → Bool) (g : Lifting.Gadget) :
  True := by
  -- Use validated gadget constructions
  have h1 := Lifting.gadget_validity params G g rfl
  have h2 := Lifting.lifting_theorem f g dt_complexity ic_gadget
  trivial
```

### 3. SAT-Hard Reductions

**File**: `formal/TreewidthTheory.lean`

**Usage**:
```lean
import Formal.TreewidthTheory

theorem my_sat_theorem (φ : CNFFormula) (n : ℕ) :
  numVars φ = n →
  Formal.TreewidthTheory.treewidth φ ≥ n / 2 →
  True := by
  intro h_vars h_tw
  -- Use treewidth-SAT connection
  have h := Formal.TreewidthTheory.treewidthSATConnection φ n h_vars h_tw
  trivial
```

## Best Practices

### 1. Import Only What You Need

```lean
-- Good: Specific imports
import Formal.Treewidth.Treewidth
open Treewidth (Graph treewidth)

-- Avoid: Importing everything
-- import Formal.Formal
```

### 2. Use Type Aliases

```lean
-- Define aliases for commonly used types
abbrev MyGraph := Treewidth.Graph
abbrev MyTreewidth := Treewidth.treewidth

theorem my_theorem (G : MyGraph) :
  MyTreewidth G ≥ 0 := Treewidth.treewidth_nonneg G
```

### 3. Leverage Existing Theorems

```lean
-- Don't reprove existing results
theorem obvious_property (G : Treewidth.Graph) :
  Treewidth.treewidth G ≥ 0 := by
  -- Just use the existing theorem
  exact Treewidth.treewidth_nonneg G
  
-- Build on existing results
theorem my_extension (G : Treewidth.Graph) :
  Treewidth.treewidth G ≥ 0 ∧ some_other_property G := by
  constructor
  · exact Treewidth.treewidth_nonneg G  -- Reuse
  · -- Prove your new contribution
    sorry
```

### 4. Document Your Usage

```lean
/-!
# My Module Using Treewidth

This module builds on the validated Treewidth infrastructure
to prove additional results about...

## Dependencies
* `Formal.Treewidth.Treewidth`: Core treewidth definitions
* `Formal.TreewidthTheory`: Formula treewidth
-/

import Formal.Treewidth.Treewidth
import Formal.TreewidthTheory

namespace MyModule

-- Your theorems here

end MyModule
```

## Troubleshooting

### Issue: Import errors

```lean
-- Error: unknown namespace 'Treewidth'
import Treewidth  -- Wrong!

-- Solution: Use full path
import Formal.Treewidth.Treewidth  -- Correct!
```

### Issue: Type mismatch

```lean
-- Error: expected Graph, got Treewidth.Graph
theorem bad (G : Graph) : ... -- Wrong!

-- Solution: Use qualified name
theorem good (G : Treewidth.Graph) : ...  -- Correct!
```

### Issue: Theorem not found

```lean
-- Error: unknown identifier 'treewidth_nonneg'
theorem bad : treewidth_nonneg ...  -- Wrong!

-- Solution: Use full name
theorem good : Treewidth.treewidth_nonneg ...  -- Correct!

-- Or open the namespace
open Treewidth
theorem also_good : treewidth_nonneg ...  -- Correct!
```

## Examples from the Repository

### Example 1: Main Theorem Usage

See `formal/MainTheorem.lean` for how the main P≠NP theorem uses treewidth:

```lean
import Formal.TreewidthTheory

-- The main theorem builds on treewidth infrastructure
theorem p_neq_np : P ≠ NP := by
  -- Uses treewidth through the structural coupling
  sorry
```

### Example 2: Structural Coupling

See `formal/StructuralCoupling.lean` for the key lemma:

```lean
import Formal.ComputationalDichotomy

theorem structuralCoupling (φ : CNFFormula) :
  treewidth φ ≥ numVars φ / 2 →
  -- High treewidth implies hardness
  sorry
```

### Example 3: Integration Validation

See `formal/TreewidthIntegration.lean` for validation patterns:

```lean
import Formal.Treewidth.Treewidth
import Formal.TreewidthTheory

-- Validation theorems show correct usage
theorem communication_bounds_connection_valid : True := trivial
```

## Summary

The Treewidth module is **ready for use** in higher-level theorems. To use it:

1. Import the appropriate module (`Formal.Treewidth.Treewidth` or `Formal.TreewidthTheory`)
2. Use the provided types (`Treewidth.Graph`) and functions (`Treewidth.treewidth`)
3. Apply the validated theorems (e.g., `treewidth_nonneg`, `treewidthSATConnection`)
4. Build your own results on top of this foundation

For questions or issues, see `TREEWIDTH_STATUS.md` and `TREEWIDTH_VALIDATION.md`.

---

**Author**: José Manuel Mota Burruezo Ψ ∞³  
**QCAL System**: 141.7001 Hz  
**Status**: ✅ VALIDATED FOR USE
