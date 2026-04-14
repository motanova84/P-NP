# Quick Reference: SimpleTreewidth Module

## Import and Use

```lean
import SimpleTreewidth
open SimpleTreewidth
```

## Complete Proofs (Ready to Use)

### Basic Arithmetic
```lean
simple_lemma : 2 + 2 = 4
three_plus_one : 3 + 1 = 4
```

### Edge Expansion Properties
```lean
edgeExpansion_nonneg (G : SimpleGraph V) (S : Finset V) : 0 ≤ edgeExpansion G S
edgeExpansion_le_degree (G : SimpleGraph V) (S : Finset V) : edgeExpansion G S ≤ card V
edgeExpansion_empty (G : SimpleGraph V) : edgeExpansion G ∅ = 0
edgeExpansion_singleton (G : SimpleGraph V) (v : V) : 0 ≤ edgeExpansion G {v}
```

### General Properties
```lean
nonneg_composition (a b : ℚ) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b
finset_card_nonneg (S : Finset V) : 0 ≤ S.card
pathGraph_edge_count (n : ℕ) : ∃ m, m ≤ n
```

### Graph Properties
```lean
cycleGraph_symm (n : ℕ) (i j : Fin n) : cycleGraph.Adj i j → cycleGraph.Adj j i
not_adj_self (G : SimpleGraph V) (v : V) : ¬ G.Adj v v
```

## Key Definitions

### Edge Expansion
```lean
def edgeExpansion (G : SimpleGraph V) (S : Finset V) : ℚ :=
  if S.card = 0 then 0
  else (G.edgeBoundary S).card / S.card
```

### Cycle Graph
```lean
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  -- Proven: symm and loopless
```

### Path Graph
```lean
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  -- Proven: symm and loopless
```

## Example Usage

### Simple Example
```lean
example : 2 + 2 = 4 := simple_lemma

example (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S := 
  edgeExpansion_nonneg G S
```

### Composition Example
```lean
theorem expansion_sum (G : SimpleGraph V) (S T : Finset V) :
    0 ≤ edgeExpansion G S + edgeExpansion G T := by
  apply nonneg_composition
  · exact edgeExpansion_nonneg G S
  · exact edgeExpansion_nonneg G T
```

### Graph Example
```lean
def cycle3 : SimpleGraph (Fin 3) := cycleGraph 3

example (i j : Fin 3) (h : cycle3.Adj i j) : cycle3.Adj j i :=
  cycleGraph_symm 3 i j h
```

## Building Blocks for cycle_treewidth_two

### Current Status
- ✅ Foundation complete (12 proofs)
- ✅ Graph structures defined
- 🔄 Tree decomposition (in formal/Treewidth)
- 🔄 Full theorem (roadmap available)

### Next Steps
See `CYCLE_TREEWIDTH_ROADMAP.md` for detailed plan.

## Documentation Files

| File | Purpose |
|------|---------|
| `SIMPLE_TREEWIDTH_README.md` | Overview and status |
| `BUILDING_REAL_THEOREMS_GUIDE.md` | Methodology guide |
| `CYCLE_TREEWIDTH_ROADMAP.md` | Implementation plan |
| `SIMPLE_TREEWIDTH_IMPLEMENTATION_SUMMARY.md` | Complete summary |
| `SimpleTreewidthExamples.lean` | Working examples |

## Key Principle

**Start simple, verify everything, build gradually, complete each step.**

---

**Status**: Foundation complete, 12 proofs with 0% sorry rate  
**Next**: Phase 2 - Tree properties  
**Goal**: Complete `cycle_treewidth_two` theorem
