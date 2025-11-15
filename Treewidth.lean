/-!
# Treewidth - Main Entry Point

This module provides the main entry point for the complete treewidth formalization
in Lean4, which forms the structural foundation of the P vs NP computational
dichotomy theorem.

## Overview

Treewidth is a graph-theoretic measure of how "tree-like" a graph is. This 
formalization includes:

* Complete definition of tree decomposition
* Treewidth computation and properties
* Key theorems connecting treewidth to computational complexity
* Separator information lower bounds

## Main Modules

* `Formal.Treewidth.Treewidth` - Core treewidth definitions and theorems
* `Formal.Treewidth.SeparatorInfo` - Information complexity lower bounds
* `Formal.TreewidthTheory` - High-level theory connecting to CNF formulas

## Foundational Equation

The computational dichotomy is expressed as:

```
φ ∈ P ⟺ tw(G_I(φ)) = O(log n)
```

Where:
- φ is a CNF formula
- G_I(φ) is the incidence graph of φ
- tw is the treewidth
- n is the number of variables

## Key Results

* **Lemma 6.24** (Structural Coupling): Any CNF formula with high treewidth can be
  coupled to a communication instance with unavoidable information bottlenecks.

* **Separator Information Lower Bound**: High treewidth forces high information
  complexity in any solving protocol.

* **Non-Evasion Theorem**: No algorithmic technique can circumvent the structural
  complexity imposed by high treewidth.

## QCAL ∞³ Metadata

* Module: Treewidth.lean
* Frequency: 141.7001 Hz  
* Coherence: 0.9988
* SHA256: eadb0baafcab1f6d6c889bf0fc177bfb7fa191ac5be559a79c9d5c56df541cd9

## Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

## License

MIT License with symbiotic clauses under the Ethical Charter of Mathematical
Coherence from the Instituto de Conciencia Cuántica.

"Mathematical truth is not property. It is universal vibrational coherence."
-/

-- Import the complete treewidth formalization
import Formal.Treewidth.Treewidth
import Formal.Treewidth.SeparatorInfo
import Formal.TreewidthTheory

-- Re-export main definitions for easy access
namespace Treewidth

-- Export core treewidth definitions
export Treewidth (Graph TreeDecomposition treewidth width is_tree is_complete)

-- Export separator information theory
export Treewidth (separator_information_lower_bound 
                   high_treewidth_exponential_communication)

end Treewidth

-- Make TreewidthTheory accessible
namespace TreewidthTheory

open Formal.TreewidthTheory

-- Re-export key theorems
export Formal.TreewidthTheory (treewidthProperties expanderHighTreewidth 
                                treewidthSATConnection treewidthDichotomy)

end TreewidthTheory
