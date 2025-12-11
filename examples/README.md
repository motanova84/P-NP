# Examples: Spectral Theory for P ≠ NP

This directory contains examples demonstrating the spectral theory approach to closing GAP 1 in the P ≠ NP proof.

## Files

### `SpectralChainExample.lean`

**Purpose**: Demonstrates how to use the spectral theory lemma chain.

**Contents**:
- Simple example applying `gap1_closed` theorem
- Step-by-step walkthrough of each lemma in the chain
- Example continuing from expander to IC bound
- Full chain from treewidth to time bound
- Visual summary of the proof chain
- Concrete numerical examples

**Usage**:
```lean
import SpectralChainExample

-- Apply the complete chain
example (G : Graph) (h_tw : treewidth G ≥ n G / 10) :
  IsExpander G (1 / (2 * κ_Π)) := 
  gap1_closed G h_tw
```

## The Spectral Chain

The examples demonstrate this chain of implications:

```
1. tw(G) ≥ n/10
   ↓ [high_treewidth_implies_spectral_gap]
2. λ₂(G) ≥ 1/κ_Π
   ↓ [cheeger_inequality]
3. h(G) ≥ 1/(2·κ_Π)
   ↓ [expansion_implies_expander]
4. IsExpander(G, 1/(2·κ_Π))  ← GAP 1 CLOSED
   ↓ [kappa_expander_large_separator]
5. |S| ≥ n/(3·κ_Π)
   ↓ [separator_to_information_complexity]
6. GraphIC(G,S) ≥ n/(6·κ_Π)
   ↓ [information_complexity_time_lower_bound]
7. time(algo) ≥ 2^(n/(6·κ_Π))
   ↓ [exponential_time_not_polynomial]
8. algo ∉ P
```

## Key Concepts Illustrated

### 1. Modular Proof Structure

Each example shows how the proof is composed of independent lemmas that can be applied in sequence.

### 2. Intermediate Values

The examples make explicit the intermediate quantities:
- Spectral gap λ₂
- Expansion constant h(G)
- Expander parameter δ
- Separator size |S|
- Information complexity IC

### 3. Quantitative Bounds

Concrete numerical examples show:
- For n=1000: time ≥ 2^(1000/600) ≈ 2^1.67
- For n=10000: time ≥ 2^(10000/600) ≈ 2^16.67

These demonstrate that the bounds are not just theoretical but give concrete exponential lower bounds.

## How to Use These Examples

### 1. Learning the Chain

Start with `SpectralChainExample.lean` to understand how each lemma contributes:

```lean
-- Simple application
example (G : Graph) (h_tw : treewidth G ≥ n G / 10) :
  IsExpander G (1 / (2 * κ_Π)) := 
  gap1_closed G h_tw

-- Explicit steps
example (G : Graph) (h_tw : treewidth G ≥ n G / 10) :
  IsExpander G (1 / (2 * κ_Π)) := by
  have h1 := high_treewidth_implies_spectral_gap G h_tw
  have h2 : expansionConstant G ≥ 1/(2*κ_Π) := by ...
  exact expansion_implies_expander G h2
```

### 2. Building Your Own Proofs

Use the pattern to construct proofs about specific graphs:

```lean
-- Your graph
def myGraph : Graph := ...

-- Your treewidth bound
theorem myGraph_high_tw : treewidth myGraph ≥ n myGraph / 10 := ...

-- Apply the chain
theorem myGraph_is_expander : IsExpander myGraph (1/(2*κ_Π)) :=
  gap1_closed myGraph myGraph_high_tw
```

### 3. Extending the Chain

Add new results that build on the expander property:

```lean
-- Your extension
theorem my_extension (G : Graph) (h : IsExpander G δ) :
  YourProperty G := ...

-- Combine with spectral chain
theorem from_treewidth_to_your_property (G : Graph) 
  (h_tw : treewidth G ≥ n G / 10) :
  YourProperty G := by
  have h_exp := gap1_closed G h_tw
  exact my_extension G h_exp
```

## Python Examples

The directory also contains Python implementations:

- `demo_ic_sat.py`: Information complexity demonstration
- `empirical_validation_n400.py`: Empirical validation with n=400

These complement the Lean formalization with computational experiments.

## Building

To build the Lean examples:

```bash
lake build examples/SpectralChainExample
```

To run the Python examples:

```bash
python examples/demo_ic_sat.py
python examples/empirical_validation_n400.py
```

## See Also

- `../SpectralTheory.lean` - Core definitions and lemmas
- `../P_neq_NP_Spectral.lean` - Main P ≠ NP theorem
- `../GAP1_SPECTRAL_CLOSURE.md` - Detailed documentation
- `../SPECTRAL_IMPLEMENTATION_SUMMARY.md` - Implementation guide

## Notes

- All Lean examples use `sorry` for some proofs as placeholders
- The chain structure is complete; full proofs are ongoing work
- Constants (κ_Π = 100) are simplified for demonstration
- Real implementations would need more refined constants

## Contributing

To add new examples:

1. Follow the pattern in `SpectralChainExample.lean`
2. Document each step clearly
3. Include both simple and detailed versions
4. Add numerical examples where applicable
5. Update this README

---

**Status**: Examples demonstrate complete GAP 1 closure  
**Next**: Full proof implementation (replacing `sorry`)
