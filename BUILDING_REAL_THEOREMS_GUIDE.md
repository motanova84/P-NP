# Building Real Theorems: A Methodological Guide

## The Problem

Many Lean4 formalizations suffer from:
- **Too many `sorry`s**: Incomplete proofs everywhere
- **Assumed definitions**: Using things that don't exist in Mathlib
- **Top-down approach**: Starting with complex theorems before proving basics
- **Lack of validation**: No way to verify what actually works

## The Solution: Incremental Building

### Step 1: Start Ridiculously Simple

```lean
lemma simple_lemma : 2 + 2 = 4 := by norm_num
```

**Why?** This proves your tactics work and the file compiles.

### Step 2: Verify What Exists

```lean
#check SimpleGraph.Adj           -- ✓ Exists in Mathlib
#check SimpleGraph.edgeExpansion  -- ✗ Does NOT exist
```

**Before** using any definition, verify it's actually in Mathlib!

### Step 3: Define What's Missing

```lean
def edgeExpansion (G : SimpleGraph V) (S : Finset V) : ℚ :=
  if S.card = 0 then 0
  else (G.edgeBoundary S).card / S.card
```

If something doesn't exist, define it yourself with:
- Clear purpose
- Sensible defaults (handle edge cases)
- Simple implementation

### Step 4: Prove Simple Properties FIRST

```lean
lemma edgeExpansion_nonneg (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S := by
  unfold edgeExpansion
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
```

**Complete this proof** before moving to anything more complex!

### Step 5: Build Incrementally

Layer your complexity:

1. **Trivial facts**: `2 + 2 = 4`
2. **Basic properties**: Non-negativity, symmetry
3. **Simple structures**: Path graphs, cycles
4. **Compositions**: Combining simple results
5. **Target theorem**: The actual goal

## Anti-Patterns to Avoid

### ❌ Don't Do This

```lean
-- BAD: Starting with the hardest theorem
theorem cycle_treewidth_two (n : ℕ) (hn : n ≥ 3) :
    (cycleGraph n).treewidth = 2 := by
  sorry -- TODO: figure this out later
```

### ✅ Do This Instead

```lean
-- GOOD: Build the foundation first
lemma cycleGraph_symm (n : ℕ) (i j : Fin n) :
    (cycleGraph n).Adj i j → (cycleGraph n).Adj j i := by
  intro h
  exact (cycleGraph n).symm h

-- Then build up to the full theorem
```

## The Verification Checklist

Before considering a theorem "done":

- [ ] Does it compile?
- [ ] Are all tactics valid?
- [ ] Is every `sorry` justified?
- [ ] Can you state a simpler version?
- [ ] Have you tested with examples?
- [ ] Is it documented?

## Practical Examples from SimpleTreewidth.lean

### Example 1: Complete Proof

```lean
lemma edgeExpansion_empty (G : SimpleGraph V) :
    edgeExpansion G ∅ = 0 := by
  unfold edgeExpansion
  simp
```

**Status**: ✅ Complete - No sorry!

### Example 2: Incremental Building

```lean
-- Level 1: Basic fact
lemma finset_card_nonneg (S : Finset V) : 0 ≤ S.card := by
  exact Nat.zero_le _

-- Level 2: Use it
lemma edgeExpansion_nonneg (G : SimpleGraph V) (S : Finset V) : 
    0 ≤ edgeExpansion G S := by
  -- Uses finset_card_nonneg implicitly
  ...
```

### Example 3: Composition

```lean
lemma nonneg_composition (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b := by
  exact add_nonneg ha hb

-- Then use it:
theorem expansion_properties (G : SimpleGraph V) (S T : Finset V) :
    0 ≤ edgeExpansion G S + edgeExpansion G T := by
  apply nonneg_composition
  · exact edgeExpansion_nonneg G S
  · exact edgeExpansion_nonneg G T
```

## Measuring Progress

### Metrics That Matter

1. **Complete Proofs**: How many lemmas have zero `sorry`s?
2. **Dependency Depth**: Can you prove X using only proven lemmas?
3. **Example Coverage**: Do concrete examples work?

### Don't Measure

1. ~~Total lines of code~~
2. ~~Number of theorems (if they're all `sorry`)~~
3. ~~Complexity of statements (if unproven)~~

## The Path to cycle_treewidth_two

Our target theorem:

```lean
theorem cycle_treewidth_two (n : ℕ) (hn : n ≥ 3) :
    (cycleGraph n).treewidth = 2
```

### Completed Prerequisites (✅)

1. ✅ `cycleGraph` is defined
2. ✅ `cycleGraph_symm` is proven
3. ✅ Basic graph properties work
4. ✅ Edge expansion machinery exists

### Remaining Steps (🔄)

1. 🔄 Define tree decomposition properly
2. 🔄 Construct decomposition for cycle with width 2
3. 🔄 Prove lower bound (needs 2 bags)
4. 🔄 Combine for exact result

### How to Proceed

**Don't** jump to the full theorem. **Do** prove:

```lean
-- Next step
lemma cycle_has_decomposition_width_2 (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : TreeDecomposition (cycleGraph n), width D ≤ 2 := by
  -- Explicit construction
```

Then:

```lean
lemma cycle_needs_width_2 (n : ℕ) (hn : 3 ≤ n) :
    ∀ D : TreeDecomposition (cycleGraph n), width D ≥ 2 := by
  -- Prove you need at least 2
```

Finally combine them!

## Tools and Techniques

### Useful Tactics

- `norm_num` - For numerical goals
- `simp` - For simplification
- `omega` - For linear arithmetic
- `exact` - When you have exactly what you need
- `apply` - To use a lemma
- `unfold` - To expand definitions

### Useful Patterns

```lean
-- Case splitting
split_ifs with h
· -- case when condition is true
· -- case when condition is false

-- Contradiction
cases hEmpty
contradiction

-- Calculation chains
calc x = y := by ...
     _ = z := by ...
     _ = w := by ...
```

## Summary

**The mantra**: 

> Start simple. Verify everything. Build incrementally. Complete each step.

**The result**: 

Real, working, verified mathematics that builds confidence and enables further progress.

## Resources

- **SimpleTreewidth.lean**: The implementation
- **SimpleTreewidthExamples.lean**: Working examples
- **SIMPLE_TREEWIDTH_README.md**: Overview
- This file: Methodology

Start here, build carefully, achieve real results! 🎯
