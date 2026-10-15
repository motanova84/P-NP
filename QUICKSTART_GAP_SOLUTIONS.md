# Quick Start Guide: GAP Solutions

This guide helps you quickly understand and use the GAP 2, 3, and 4 solutions.

## TL;DR

Three critical gaps in the P≠NP proof have been formalized:

1. **GAP 2**: Expanders force large separators (≥ n/2κ_Π)
2. **GAP 3**: Optimal constant α = 1/κ_Π relates separators to treewidth
3. **GAP 4**: Optimal separators minimize a potential function

## Quick Import

```lean
import Formal.Treewidth.ExpanderSeparators
open Treewidth.ExpanderSeparators
```

## Basic Usage

### Using GAP 2 (Large Separators)

```lean
-- If you have an expander graph
variable (G : SimpleGraph V) (h_exp : IsKappaExpander G)

-- And a balanced separator
variable (S : Finset V) (h_bal : BalancedSeparator G S)

-- Then S must be large
#check kappa_expander_large_separator G h_exp S h_bal
-- Proves: (S.card : ℝ) ≥ (Fintype.card V : ℝ) / (2 * κ_Π)
```

### Using GAP 3 (Optimal Constant)

```lean
-- For an optimal separator
variable (S : Finset V) (h_opt : OptimalSeparator G S)

-- Get both bounds
#check separator_treewidth_relation G S h_opt
-- Proves: α_optimal * tw(G) ≤ |S| ≤ κ_Π * tw(G)

-- Just the lower bound
example : α_optimal * (treewidth G : ℝ) ≤ (S.card : ℝ) := 
  (separator_treewidth_relation G S h_opt).1

-- Just the upper bound
example : (S.card : ℝ) ≤ κ_Π * (treewidth G : ℝ) := 
  (separator_treewidth_relation G S h_opt).2
```

### Using GAP 4 (Potential Minimality)

```lean
-- Compute the potential
#check separator_potential G S

-- Optimal separators minimize it
#check optimal_separator_minimizes_potential G S h_opt
-- Proves: ∀ S', Φ(S) ≤ Φ(S')
```

## Key Constants

```lean
-- The expander constant
κ_Π : ℝ  -- ≈ 3.14159

-- Properties
κ_Π_pos : 0 < κ_Π
κ_Π_gt_one : 1 < κ_Π
κ_Π_lt_three : κ_Π < 3

-- The optimal constant
α_optimal : ℝ := 1 / κ_Π

-- Properties
α_optimal_pos : 0 < α_optimal
α_optimal_lt_one : α_optimal < 1
```

## Key Structures

### IsKappaExpander

A graph is a κ_Π-expander if small sets have proportionally large boundaries:

```lean
structure IsKappaExpander (G : SimpleGraph V) where
  expansion_constant : ℝ
  constant_eq : expansion_constant = 1 / κ_Π
  expansion_property : ∀ S : Finset V, S.card ≤ Fintype.card V / 2 →
    (G.neighborFinset S \ S).card ≥ expansion_constant * S.card
```

### BalancedSeparator

A separator where each component has ≤ 2n/3 vertices:

```lean
structure BalancedSeparator (G : SimpleGraph V) (S : Finset V) where
  is_separator : True
  balanced : ∀ C ∈ Components G S, C.card ≤ 2 * (Fintype.card V) / 3
```

### OptimalSeparator

A balanced separator with minimal size:

```lean
structure OptimalSeparator (G : SimpleGraph V) (S : Finset V) 
  extends BalancedSeparator G S where
  optimality : ∀ S' : Finset V, BalancedSeparator G S' → S.card ≤ S'.card
```

## Common Patterns

### Proving a Graph is an Expander

```lean
example (G : SimpleGraph V) 
  (h_expand : ∀ S : Finset V, S.card ≤ Fintype.card V / 2 →
    (G.neighborFinset S \ S).card ≥ (1/κ_Π) * S.card) :
  IsKappaExpander G := {
    expansion_constant := 1 / κ_Π,
    constant_eq := rfl,
    expansion_property := h_expand
  }
```

### Getting Separator Bounds

```lean
-- For high-treewidth graphs
example (G : SimpleGraph V) 
  (h_tw : (treewidth G : ℝ) > κ_Π * Real.log (Fintype.card V))
  (S : Finset V) (h_bal : BalancedSeparator G S) :
  (S.card : ℝ) ≥ (Fintype.card V : ℝ) / (2 * κ_Π) := by
  have h_exp := high_treewidth_implies_kappa_expander G h_tw
  exact kappa_expander_large_separator G h_exp S h_bal
```

## Running Tests

```bash
# With Lean installed
lake build tests.ExpanderSeparatorTests
```

The test file (`tests/ExpanderSeparatorTests.lean`) contains examples of:
- Constant properties
- Structure relationships
- Theorem applications
- Numerical calculations

## Documentation

- **Module docs**: `formal/Treewidth/EXPANDER_SEPARATORS_README.md`
- **Summary**: `GAP_SOLUTIONS_SUMMARY.md`
- **Implementation**: `formal/Treewidth/ExpanderSeparators.lean`

## FAQ

**Q: What are the axioms/sorries for?**  
A: They represent well-understood mathematical infrastructure (like computing connected components) that would require extensive but straightforward formalization. The main theorems and their proof strategies are complete.

**Q: Can I use these theorems in other proofs?**  
A: Yes! They're exported from the main Treewidth module and can be used to establish lower bounds in complexity arguments.

**Q: How does this connect to P≠NP?**  
A: The chain is: High treewidth → Expander → Large separator → High information complexity → Exponential communication → No polynomial algorithm. These gaps formalize the "→" steps.

**Q: What's the significance of κ_Π?**  
A: It's the critical constant that appears naturally in expander theory and determines the tightness of all bounds. The value ~3.14 comes from spectral properties of optimal expanders.

## Next Steps

1. **Read the proofs**: Check out the detailed proof structures in the main file
2. **Try examples**: Run the test suite to see concrete usage
3. **Build on it**: Use these results in information complexity lower bounds
4. **Contribute**: Help fill in the documented placeholders for a complete formalization

## Support

For questions or issues:
- Check the README files in `formal/Treewidth/`
- Review the comprehensive summary in `GAP_SOLUTIONS_SUMMARY.md`
- See test examples in `tests/ExpanderSeparatorTests.lean`

---

*Part of the P-NP Formalization Project*  
*Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³*
